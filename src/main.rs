use clap::Parser;
use k256::{
    ecdsa::{SigningKey, VerifyingKey},
};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use sha3::{Digest, Keccak256};
use std::{
    collections::{HashMap, VecDeque},
    fs,
    io::{Read, Write},
    net::{IpAddr, Ipv6Addr, SocketAddr, TcpListener, TcpStream},
    sync::{
        atomic::{AtomicBool, AtomicI64, AtomicUsize, Ordering},
        Arc, Condvar, Mutex,
    },
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

// Struct untuk menyimpan argumen CLI (pengganti flag)
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Pattern to search for (hex, no 0x)
    #[arg(long, default_value = "")]
    pattern: String,

    /// Mode: prefix or suffix
    #[arg(long, default_value = "prefix")]
    mode: String,

    /// Output file
    #[arg(long, default_value = "vanity_results.json")]
    out: String,

    /// How many to find
    #[arg(long, default_value_t = 1)]
    count: usize,

    /// HTTP monitor port (default 80)
    #[arg(long, default_value_t = 80)]
    monitor_port: u16,
}

// Struct untuk hasil JSON
#[derive(Serialize, Deserialize, Debug, Clone)]
struct ResultEntry {
    address: String,
    private_key: String,
    pattern: String,
    mode: String,
    attempts: i64,
    timestamp: u64,
    elapsed_seconds: i64,
}

#[derive(Serialize, Debug, Clone)]
struct FoundSummary {
    address: String,
    attempts: i64,
    elapsed_seconds: i64,
    timestamp: u64,
}

const AUTH_COOKIE_NAME: &str = "vanity_auth";
const AUTH_COOKIE_VALUE: &str = "granted";
const AUTH_SECRET: &str = "atomic";

#[derive(Clone, Serialize, Debug)]
struct JobSnapshot {
    id: u64,
    pattern: String,
    mode: String,
    count: usize,
    submitted_at: u64,
}

#[derive(Clone)]
struct JobSpec {
    id: u64,
    pattern: String,
    mode: String,
    count: usize,
    submitted_at: u64,
    cancel_flag: Arc<AtomicBool>,
}

impl JobSpec {
    fn snapshot(&self) -> JobSnapshot {
        JobSnapshot {
            id: self.id,
            pattern: self.pattern.clone(),
            mode: self.mode.clone(),
            count: self.count,
            submitted_at: self.submitted_at,
        }
    }
}

#[derive(Serialize, Debug)]
struct StatusResponse {
    current_job: Option<JobSnapshot>,
    pending_jobs: Vec<JobSnapshot>,
    found_current: usize,
    attempts_current: i64,
    attempts_total: i64,
    attempts_per_second: f64,
    elapsed_seconds: f64,
    status: String,
    last_found: Option<FoundSummary>,
    results_file: String,
    timestamp: u64,
}

struct JobRuntimeMetrics {
    job_id: u64,
    start_instant: Instant,
}

#[derive(Debug, Clone, Copy)]
enum CancelStatus {
    Active,
    Pending,
    NotFound,
}

struct JobQueueState {
    active_job: Option<JobSpec>,
    pending_jobs: VecDeque<JobSpec>,
    next_job_id: u64,
    shutdown: bool,
}

impl JobQueueState {
    fn new() -> Self {
        Self {
            active_job: None,
            pending_jobs: VecDeque::new(),
            next_job_id: 0,
            shutdown: false,
        }
    }

    fn enqueue(&mut self, pattern: String, mode: String, count: usize) -> JobSpec {
        self.next_job_id += 1;
        let spec = JobSpec {
            id: self.next_job_id,
            pattern,
            mode,
            count,
            submitted_at: current_unix_ts(),
            cancel_flag: Arc::new(AtomicBool::new(false)),
        };
        self.pending_jobs.push_back(spec.clone());
        spec
    }

    fn clear_active(&mut self, job_id: u64) {
        if let Some(active) = &self.active_job {
            if active.id == job_id {
                self.active_job = None;
            }
        }
    }

    fn cancel_job(&mut self, job_id: u64) -> CancelStatus {
        if let Some(active) = self.active_job.as_mut() {
            if active.id == job_id {
                active.cancel_flag.store(true, Ordering::Relaxed);
                return CancelStatus::Active;
            }
        }

        if let Some(idx) = self.pending_jobs.iter().position(|job| job.id == job_id) {
            self.pending_jobs.remove(idx);
            return CancelStatus::Pending;
        }

        CancelStatus::NotFound
    }
}

type JobQueueHandle = Arc<(Mutex<JobQueueState>, Condvar)>;

fn decode_form_value(value: &str) -> String {
    let mut result = String::new();
    let mut chars = value.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '+' => result.push(' '),
            '%' => {
                let hi = chars.next();
                let lo = chars.next();
                if let (Some(h), Some(l)) = (hi, lo) {
                    let mut hex = String::new();
                    hex.push(h);
                    hex.push(l);
                    if let Ok(byte) = u8::from_str_radix(&hex, 16) {
                        result.push(byte as char);
                    }
                }
            }
            _ => result.push(ch),
        }
    }
    result
}

fn parse_form_urlencoded(body: &str) -> HashMap<String, String> {
    let mut map = HashMap::new();
    for pair in body.split('&') {
        if pair.is_empty() {
            continue;
        }
        let mut iter = pair.splitn(2, '=');
        let key = iter.next().unwrap_or_default();
        let value = iter.next().unwrap_or_default();
        map.insert(
            decode_form_value(key),
            decode_form_value(value),
        );
    }
    map
}

fn sanitize_pattern(input: &str) -> Result<String, String> {
    let trimmed = input.trim().to_lowercase();
    if trimmed.is_empty() {
        return Err("Pattern wajib diisi".to_string());
    }
    if trimmed.len() > 40 {
        return Err("Pattern maksimal 40 karakter hex".to_string());
    }
    if !trimmed.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err("Pattern harus berupa hex (0-9a-f)".to_string());
    }
    Ok(trimmed)
}

fn normalize_mode(input: &str) -> Result<String, String> {
    let lowered = input.trim().to_lowercase();
    match lowered.as_str() {
        "prefix" | "suffix" => Ok(lowered),
        _ => Err("Mode harus prefix atau suffix".to_string()),
    }
}

fn parse_count(value: &str) -> Result<usize, String> {
    let parsed = value.trim().parse::<usize>().map_err(|_| "Count tidak valid".to_string())?;
    if parsed == 0 || parsed > 50 {
        return Err("Count harus antara 1-50".to_string());
    }
    Ok(parsed)
}

fn has_valid_cookie(request: &str) -> bool {
    for line in request.lines() {
        if line.to_ascii_lowercase().starts_with("cookie:") {
            if line.contains(&format!("{}={}", AUTH_COOKIE_NAME, AUTH_COOKIE_VALUE)) {
                return true;
            }
        }
    }
    false
}

// Fungsi helper untuk mendapatkan hex dari private key
fn priv_to_hex(secret_key: &SigningKey) -> String {
    hex::encode(secret_key.to_bytes())
}

// Fungsi helper untuk mendapatkan address dari public key
fn pub_to_address(verifying_key: &VerifyingKey) -> String {
    // Encode point uncompressed (false) -> return bytes [tag, x..., y...]
    let encoded = verifying_key.to_encoded_point(false);
    let bytes = encoded.as_bytes();
    
    // Drop byte pertama (0x04 tag) sesuai standar Ethereum
    let public_key_bytes = &bytes[1..];

    // Keccak256 hash
    let mut hasher = Keccak256::new();
    hasher.update(public_key_bytes);
    let result = hasher.finalize();

    // Ambil 20 byte terakhir
    let address_bytes = &result[12..];
    hex::encode(address_bytes)
}

// Safer append logic: baca -> append -> tulis ulang
fn save_append(file_path: &str, rec: &ResultEntry) -> std::io::Result<()> {
    let mut arr: Vec<ResultEntry> = Vec::new();

    // Coba baca file yang ada
    if let Ok(content) = fs::read_to_string(file_path) {
        if !content.is_empty() {
            if let Ok(parsed) = serde_json::from_str(&content) {
                arr = parsed;
            }
        }
    }

    // Append record baru (perlu clone karena ResultEntry punya String)
    arr.push(ResultEntry {
        address: rec.address.clone(),
        private_key: rec.private_key.clone(),
        pattern: rec.pattern.clone(),
        mode: rec.mode.clone(),
        attempts: rec.attempts,
        timestamp: rec.timestamp,
        elapsed_seconds: rec.elapsed_seconds,
    });

    // Tulis ulang dengan indentasi
    let data = serde_json::to_string_pretty(&arr)?;
    fs::write(file_path, data)
}

fn current_unix_ts() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

fn load_history(file_path: &str) -> Vec<ResultEntry> {
    if let Ok(content) = fs::read_to_string(file_path) {
        if let Ok(parsed) = serde_json::from_str::<Vec<ResultEntry>>(&content) {
            return parsed;
        }
    }
    Vec::new()
}

fn delete_history_entry(file_path: &str, address: &str) -> std::io::Result<bool> {
    let mut entries = load_history(file_path);
    let original_len = entries.len();
    entries.retain(|entry| entry.address != address);
    let changed = entries.len() != original_len;
    if changed {
        let data = serde_json::to_string_pretty(&entries)?;
        fs::write(file_path, data)?;
    }
    Ok(changed)
}

fn clear_history(file_path: &str) -> std::io::Result<()> {
    fs::write(file_path, "[]")
}

fn escape_html(input: &str) -> String {
    input
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

fn format_timestamp(ts: u64) -> String {
    use chrono::Utc;
    chrono::DateTime::<Utc>::from_timestamp(ts as i64, 0)
        .unwrap_or_else(|| Utc::now())
        .format("%Y-%m-%d %H:%M:%S UTC")
        .to_string()
}

fn render_login_page(error: Option<&str>) -> String {
    let error_block = if let Some(msg) = error {
        format!(
            r#"<div class="alert">{} </div>"#,
            escape_html(msg)
        )
    } else {
        String::new()
    };

    format!(
        r#"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8" />
<title>Vanity Monitor Login</title>
<style>
body {{ font-family: "Inter", sans-serif; background:#0d1117; color:#f0f6fc; display:flex; align-items:center; justify-content:center; height:100vh; margin:0; }}
.card {{ background:#161b22; padding:32px; border-radius:12px; box-shadow:0 20px 45px rgba(0,0,0,0.45); width:360px; }}
label {{ display:block; margin-bottom:8px; font-size:0.9rem; color:#8b949e; }}
input {{ width:100%; padding:10px; border-radius:8px; border:1px solid #30363d; background:#0d1117; color:#f0f6fc; margin-bottom:16px; }}
button {{ width:100%; padding:12px; border:none; border-radius:8px; background:#238636; color:#fff; font-weight:600; cursor:pointer; }}
button:hover {{ background:#2ea043; }}
.alert {{ background:#ff555580; padding:10px 14px; border-radius:8px; margin-bottom:16px; color:#ffd7d7; font-size:0.9rem; }}
</style>
</head>
<body>
<form class="card" method="POST" action="/login">
  <h2>Auth Required</h2>
  <p style="color:#8b949e;">Masukkan kode rahasia untuk akses dashboard.</p>
  {error_block}
  <label for="code">Secret Code</label>
  <input type="password" id="code" name="code" placeholder="••••••" autocomplete="off" />
  <button type="submit">Unlock</button>
</form>
</body>
</html>"#
    )
}

fn build_history_table(entries: &[ResultEntry]) -> String {
    if entries.is_empty() {
        return "<tr><td colspan=\"8\" style=\"text-align:center;\">Belum ada data</td></tr>".to_string();
    }

    entries
        .iter()
        .rev()
        .take(200)
        .map(|entry| {
            let address = escape_html(&entry.address);
            format!(
                "<tr><td>{}</td><td><code>{}</code></td><td><code>{}</code></td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>
                    <form method=\"POST\" action=\"/history/delete\" style=\"display:inline\" onsubmit=\"return confirm('Hapus entry ini?');\">
                        <input type=\"hidden\" name=\"address\" value=\"{address}\" />
                        <button type=\"submit\" style=\"padding:6px 10px;border:none;border-radius:6px;background:#dc2626;color:white;cursor:pointer;\">Delete</button>
                    </form>
                </td></tr>",
                format_timestamp(entry.timestamp),
                &address,
                escape_html(&entry.private_key),
                escape_html(&entry.pattern),
                escape_html(&entry.mode),
                entry.attempts,
                entry.elapsed_seconds
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn render_dashboard_html(status: &StatusResponse, history: &[ResultEntry], message: Option<&str>) -> String {
    let status_pretty =
        serde_json::to_string_pretty(status).unwrap_or_else(|_| "{}".to_string());
    let history_rows = build_history_table(history);
    let message_block = if let Some(msg) = message {
        format!(
            "<div class=\"alert\">{}</div>",
            escape_html(msg)
        )
    } else {
        String::new()
    };
    let pending_html = if status.pending_jobs.is_empty() {
        "<p>Tidak ada antrian.</p>".to_string()
    } else {
        let items = status
            .pending_jobs
            .iter()
            .map(|job| {
                format!(
                    "<li>
                        <div>
                            <strong>#{}</strong> • {} • {} • target {}
                        </div>
                        <form method=\"POST\" action=\"/jobs/cancel\" style=\"margin-top:4px;\">
                            <input type=\"hidden\" name=\"job_id\" value=\"{}\" />
                            <button type=\"submit\" style=\"padding:6px 10px; border:none; border-radius:6px; background:#f97316; color:#0f172a; cursor:pointer;\">Cancel</button>
                        </form>
                    </li>",
                    job.id,
                    escape_html(&job.pattern),
                    escape_html(&job.mode),
                    job.count,
                    job.id
                )
            })
            .collect::<Vec<_>>()
            .join("");
        format!("<ul class=\"pending\">{}</ul>", items)
    };

    let current_job_summary = if let Some(job) = &status.current_job {
        format!(
            "<p>Job aktif: <strong>{}</strong> (mode: {}, target: {}, ID #{})</p>
            <form method=\"POST\" action=\"/jobs/cancel\" onsubmit=\"return confirm('Terminate job aktif?');\">
                <input type=\"hidden\" name=\"job_id\" value=\"{}\" />
                <button type=\"submit\" style=\"padding:10px 14px; border:none; border-radius:8px; background:#f87171; color:#0f172a; font-weight:600; cursor:pointer;\">Terminate Active Job</button>
            </form>",
            escape_html(&job.pattern),
            escape_html(&job.mode),
            job.count,
            job.id,
            job.id
        )
    } else {
        "<p>Tidak ada job aktif.</p>".to_string()
    };

    format!(
        r#"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8" />
<title>Vanity Dashboard</title>
<style>
body {{ font-family: "Inter", system-ui, sans-serif; background:#0b1220; color:#f4f6fb; margin:0; }}
header {{ padding:24px; background:#0f172a; box-shadow:0 2px 10px rgba(0,0,0,0.25); }}
.container {{ max-width:1100px; margin:24px auto; padding:0 16px 64px; }}
.card {{ background:#111a2e; border-radius:16px; padding:24px; margin-bottom:24px; box-shadow:0 25px 60px rgba(0,0,0,0.25); }}
label {{ display:block; margin-bottom:6px; color:#9fb3d8; font-size:0.9rem; }}
input, select {{ width:100%; padding:12px; border-radius:10px; border:1px solid #1f2a44; background:#0d1628; color:#eef3ff; margin-bottom:18px; }}
button {{ border:none; padding:12px 18px; border-radius:10px; background:#2563eb; color:white; font-weight:600; cursor:pointer; }}
button:hover {{ background:#1d4ed8; }}
.tabs {{ display:flex; gap:8px; margin-bottom:16px; }}
.tab-btn {{ flex:1; padding:12px; border-radius:10px; background:#0d1628; color:#94a3b8; border:1px solid transparent; cursor:pointer; }}
.tab-btn.active {{ background:#1d4ed8; color:white; border-color:#2563eb; }}
.tab-content {{ display:none; }}
.tab-content.active {{ display:block; animation:fade .2s ease; }}
@keyframes fade {{ from {{ opacity:0; }} to {{ opacity:1; }} }}
table {{ width:100%; border-collapse:collapse; font-size:0.9rem; }}
th, td {{ padding:10px; border-bottom:1px solid rgba(255,255,255,0.05); text-align:left; }}
th {{ text-transform:uppercase; letter-spacing:0.05em; font-size:0.75rem; color:#8da2c0; }}
code {{ background:#0d1117; padding:4px 6px; border-radius:6px; display:inline-block; }}
.alert {{ background:#1d4ed8; padding:12px; border-radius:10px; margin-bottom:16px; }}
.pending {{ list-style:none; padding-left:16px; color:#c4d2f0; }}
pre {{ background:#0d1628; padding:16px; border-radius:10px; overflow:auto; }}
.split {{ display:grid; grid-template-columns:1fr 1fr; gap:16px; }}
@media (max-width: 768px) {{
    .split {{ grid-template-columns:1fr; }}
    .tabs {{ flex-direction:column; }}
}}
</style>
</head>
<body>
<header>
  <h1>Vanity Search Dashboard</h1>
  <p>Status: <strong>{status}</strong> • Attempts: <strong>{attempts}</strong> • Rate: <strong>{rate:.1} op/s</strong> • Found: <strong>{found}</strong></p>
</header>
<div class="container">
  <div class="tabs">
    <button class="tab-btn active" data-target="tab-generate">Generate</button>
    <button class="tab-btn" data-target="tab-history">History</button>
  </div>
  <div id="tab-generate" class="tab-content active">
    <div class="card">
      <h2>Submit Pattern</h2>
      {message_block}
      <form method="POST" action="/jobs">
        <label for="pattern">Pattern (hex)</label>
        <input required id="pattern" name="pattern" placeholder="deadbeef" />
        <label for="mode">Mode</label>
        <select id="mode" name="mode">
          <option value="prefix">Prefix</option>
          <option value="suffix">Suffix</option>
        </select>
        <label for="count">Target count</label>
        <input type="number" id="count" name="count" min="1" max="50" value="1" />
        <button type="submit">Tambah ke Queue</button>
      </form>
    </div>
    <div class="card split">
      <div>
        <h3>Job Status</h3>
        {current_job_summary}
        <p>Elapsed: {elapsed:.1}s</p>
        <p>Pending Queue:</p>
        {pending_html}
      </div>
      <div>
        <h3>JSON Snapshot</h3>
        <pre>{status_json}</pre>
        <p><a href="/api/status?format=json" style="color:#93c5fd;">Lihat raw JSON</a></p>
      </div>
    </div>
  </div>
  <div id="tab-history" class="tab-content">
    <div class="card">
      <h2>History</h2>
      <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:12px;">
        <h3 style="margin:0;">History</h3>
        <form method="POST" action="/history/clear" onsubmit="return confirm('Hapus seluruh history?');">
          <button type="submit" style="padding:8px 14px; border:none; border-radius:8px; background:#dc2626; color:#fff; cursor:pointer;">Clear All</button>
        </form>
      </div>
      <table>
        <thead>
          <tr>
            <th>Timestamp</th>
            <th>Address</th>
            <th>Private Key</th>
            <th>Pattern</th>
            <th>Mode</th>
            <th>Attempts</th>
            <th>Elapsed (s)</th>
            <th>Actions</th>
          </tr>
        </thead>
        <tbody>
          {history_rows}
        </tbody>
      </table>
    </div>
  </div>
</div>
<script>
const buttons = document.querySelectorAll('.tab-btn');
const tabs = document.querySelectorAll('.tab-content');
buttons.forEach(btn => {{
    btn.addEventListener('click', () => {{
        buttons.forEach(b => b.classList.remove('active'));
        tabs.forEach(t => t.classList.remove('active'));
        btn.classList.add('active');
        document.getElementById(btn.dataset.target).classList.add('active');
    }});
}});
</script>
</body>
</html>"#,
        status = escape_html(&status.status),
        attempts = status.attempts_current,
        rate = status.attempts_per_second,
        found = status.found_current,
        elapsed = status.elapsed_seconds,
        pending_html = pending_html,
        current_job_summary = current_job_summary,
        status_json = escape_html(&status_pretty),
        history_rows = history_rows,
        message_block = message_block
    )
}

fn snapshot_jobs(job_handle: &JobQueueHandle) -> (Option<JobSnapshot>, Vec<JobSnapshot>) {
    let (lock, _) = &**job_handle;
    let state = lock.lock().unwrap();
    let current = state.active_job.as_ref().map(|job| job.snapshot());
    let pending = state
        .pending_jobs
        .iter()
        .map(|job| job.snapshot())
        .collect::<Vec<_>>();
    (current, pending)
}

fn build_status_response(
    job_handle: &JobQueueHandle,
    attempts_current: &Arc<AtomicI64>,
    attempts_total: &Arc<AtomicI64>,
    found_count: &Arc<AtomicUsize>,
    last_found: &Arc<Mutex<Option<FoundSummary>>>,
    runtime_metrics: &Arc<Mutex<Option<JobRuntimeMetrics>>>,
    results_file: &str,
) -> StatusResponse {
    let (current_job, pending_jobs) = snapshot_jobs(job_handle);
    let found_current = found_count.load(Ordering::Relaxed);
    let attempts_now = attempts_current.load(Ordering::Relaxed);
    let attempts_total_val = attempts_total.load(Ordering::Relaxed);

    let (elapsed_seconds, status_label) = if let Some(metrics) = runtime_metrics.lock().unwrap().as_ref()
    {
        (
            metrics.start_instant.elapsed().as_secs_f64(),
            if current_job.is_some() {
                "running".to_string()
            } else {
                "idle".to_string()
            },
        )
    } else if current_job.is_some() {
        (0.0, "running".to_string())
    } else if !pending_jobs.is_empty() {
        (0.0, "pending".to_string())
    } else {
        (0.0, "idle".to_string())
    };

    let attempts_per_second = if elapsed_seconds > 0.0 {
        attempts_now as f64 / elapsed_seconds
    } else {
        0.0
    };

    let last_found_value = last_found.lock().unwrap().clone();

    StatusResponse {
        current_job,
        pending_jobs,
        found_current,
        attempts_current: attempts_now,
        attempts_total: attempts_total_val,
        attempts_per_second,
        elapsed_seconds,
        status: status_label,
        last_found: last_found_value,
        results_file: results_file.to_string(),
        timestamp: current_unix_ts(),
    }
}

fn enqueue_job(job_handle: &JobQueueHandle, pattern: String, mode: String, count: usize) -> JobSpec {
    let (lock, cvar) = &**job_handle;
    let mut state = lock.lock().unwrap();
    let job = state.enqueue(pattern, mode, count);
    cvar.notify_all();
    job
}

fn cancel_job(job_handle: &JobQueueHandle, job_id: u64) -> CancelStatus {
    let (lock, cvar) = &**job_handle;
    let mut state = lock.lock().unwrap();
    let status = state.cancel_job(job_id);
    if matches!(status, CancelStatus::Pending) {
        cvar.notify_all();
    }
    status
}

fn send_http_response(
    stream: &mut TcpStream,
    status_line: &str,
    content_type: &str,
    body: &str,
    extra_headers: &[(&str, String)],
) {
    let mut response = format!(
        "{status_line}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nAccess-Control-Allow-Origin: *\r\n",
        body.as_bytes().len()
    );
    for (key, value) in extra_headers {
        response.push_str(&format!("{key}: {value}\r\n"));
    }
    response.push_str("Connection: close\r\n\r\n");
    response.push_str(body);
    let _ = stream.write_all(response.as_bytes());
}

fn send_redirect(
    stream: &mut TcpStream,
    location: &str,
    extra_headers: &[(&str, String)],
) {
    let mut headers = vec![("Location", location.to_string())];
    headers.extend_from_slice(extra_headers);
    send_http_response(stream, "HTTP/1.1 302 Found", "text/plain", "", &headers);
}

fn worker_loop(
    job_handle: JobQueueHandle,
    attempts: Arc<AtomicI64>,
    total_attempts: Arc<AtomicI64>,
    found_count: Arc<AtomicUsize>,
    last_found: Arc<Mutex<Option<FoundSummary>>>,
    runtime_metrics: Arc<Mutex<Option<JobRuntimeMetrics>>>,
    out_file: String,
    shutdown: Arc<AtomicBool>,
) {
    let mut rng = OsRng;
    loop {
        let job = {
            let (lock, cvar) = &*job_handle;
            let mut state = lock.lock().unwrap();
            loop {
                if shutdown.load(Ordering::Relaxed) || state.shutdown {
                    return;
                }
                if let Some(job) = state.active_job.clone() {
                    break job;
                }
                if let Some(next) = state.pending_jobs.pop_front() {
                    state.active_job = Some(next.clone());
                    break next;
                }
                state = cvar.wait(state).unwrap();
            }
        };

        println!(
            "\n[worker] Mulai job #{} pattern={} mode={} target={}",
            job.id, job.pattern, job.mode, job.count
        );

        attempts.store(0, Ordering::Relaxed);
        found_count.store(0, Ordering::Relaxed);
        {
            let mut metrics = runtime_metrics.lock().unwrap();
            *metrics = Some(JobRuntimeMetrics {
                job_id: job.id,
                start_instant: Instant::now(),
            });
        }
        let mut start_all = Instant::now();

        let mut job_cancelled = false;

        while found_count.load(Ordering::Relaxed) < job.count {
            if job.cancel_flag.load(Ordering::Relaxed) {
                job_cancelled = true;
                println!(
                    "[worker] Job #{} dibatalkan oleh user. Membersihkan...",
                    job.id
                );
                break;
            }

            if shutdown.load(Ordering::Relaxed) {
                return;
            }

            let private_key = SigningKey::random(&mut rng);
            let public_key = VerifyingKey::from(&private_key);
            let address_hex_clean = pub_to_address(&public_key);
            let address_hex_full = format!("0x{}", address_hex_clean);

            attempts.fetch_add(1, Ordering::Relaxed);
            total_attempts.fetch_add(1, Ordering::Relaxed);

            let body = address_hex_clean.as_str();
            let is_match = if job.mode == "prefix" {
                body.starts_with(&job.pattern)
            } else {
                body.ends_with(&job.pattern)
            };

            if is_match {
                let total_attempts_now = attempts.load(Ordering::Relaxed);
                let elapsed_sec = start_all.elapsed().as_secs() as i64;
                let unix_timestamp = current_unix_ts();

                let rec = ResultEntry {
                    address: address_hex_full,
                    private_key: priv_to_hex(&private_key),
                    pattern: job.pattern.clone(),
                    mode: job.mode.clone(),
                    attempts: total_attempts_now,
                    timestamp: unix_timestamp,
                    elapsed_seconds: elapsed_sec,
                };

                if let Err(e) = save_append(&out_file, &rec) {
                    eprintln!("\nError saving file: {}", e);
                }

                println!(
                    "[worker] FOUND (job #{}) {} attempts={} elapsed={}s",
                    job.id, rec.address, rec.attempts, rec.elapsed_seconds
                );

                let summary = FoundSummary {
                    address: rec.address.clone(),
                    attempts: rec.attempts,
                    elapsed_seconds: rec.elapsed_seconds,
                    timestamp: rec.timestamp,
                };
                if let Ok(mut slot) = last_found.lock() {
                    *slot = Some(summary);
                }

                attempts.store(0, Ordering::Relaxed);
                start_all = Instant::now();
                found_count.fetch_add(1, Ordering::Relaxed);
            }
        }

        {
            let (lock, cvar) = &*job_handle;
            let mut state = lock.lock().unwrap();
            state.clear_active(job.id);
            cvar.notify_all();
        }

        {
            let mut metrics = runtime_metrics.lock().unwrap();
            if metrics.as_ref().map(|m| m.job_id == job.id).unwrap_or(false) {
                *metrics = None;
            }
        }

        attempts.store(0, Ordering::Relaxed);
        found_count.store(0, Ordering::Relaxed);

        if job_cancelled {
            println!("[worker] Job #{} di-terminate.", job.id);
        } else {
            println!(
                "[worker] Job #{} selesai. Menunggu job berikutnya...",
                job.id
            );
        }
    }
}

fn start_http_monitor(
    port: u16,
    out_file: String,
    attempts_current: Arc<AtomicI64>,
    attempts_total: Arc<AtomicI64>,
    found_count: Arc<AtomicUsize>,
    last_found: Arc<Mutex<Option<FoundSummary>>>,
    runtime_metrics: Arc<Mutex<Option<JobRuntimeMetrics>>>,
    job_queue: JobQueueHandle,
    shutdown: Arc<AtomicBool>,
) -> std::io::Result<()> {
    let bind_addr = SocketAddr::new(IpAddr::V6(Ipv6Addr::UNSPECIFIED), port);
    let listener = TcpListener::bind(bind_addr)?;
    listener.set_nonblocking(true)?;

    println!(
        "HTTP dashboard listening on http://[::]:{} (auth code required)",
        port
    );

    while !shutdown.load(Ordering::Relaxed) {
        match listener.accept() {
            Ok((mut stream, _addr)) => {
                let mut buffer = vec![0u8; 65535];
                let read_bytes = stream.read(&mut buffer).unwrap_or(0);
                if read_bytes == 0 {
                    continue;
                }
                let request_raw = String::from_utf8_lossy(&buffer[..read_bytes]).to_string();
                let mut lines = request_raw.lines();
                let request_line = lines.next().unwrap_or("");
                let mut parts = request_line.split_whitespace();
                let method = parts.next().unwrap_or("").to_uppercase();
                let full_path = parts.next().unwrap_or("/").to_string();
                let (path_only, query_str) = if let Some(idx) = full_path.find('?') {
                    (full_path[..idx].to_string(), full_path[idx + 1..].to_string())
                } else {
                    (full_path.clone(), String::new())
                };
                let body = request_raw
                    .splitn(2, "\r\n\r\n")
                    .nth(1)
                    .unwrap_or("")
                    .trim_matches(char::from(0))
                    .to_string();
                let query_map = parse_form_urlencoded(&query_str);
                let authenticated = has_valid_cookie(&request_raw);

                if method == "POST" && path_only == "/login" {
                    let form = parse_form_urlencoded(&body);
                    let code_ok = form
                        .get("code")
                        .map(|val| val.trim() == AUTH_SECRET)
                        .unwrap_or(false);
                    if code_ok {
                        let cookie_header = format!(
                            "{}={}; Path=/; HttpOnly; SameSite=Lax",
                            AUTH_COOKIE_NAME, AUTH_COOKIE_VALUE
                        );
                        send_redirect(
                            &mut stream,
                            "/",
                            &[("Set-Cookie", cookie_header)],
                        );
                    } else {
                        let html = render_login_page(Some("Kode salah"));
                        send_http_response(
                            &mut stream,
                            "HTTP/1.1 401 Unauthorized",
                            "text/html; charset=utf-8",
                            &html,
                            &[],
                        );
                    }
                    continue;
                }

                if method == "GET" && path_only == "/logout" {
                    let cookie_header = format!(
                        "{}=deleted; Path=/; Expires=Thu, 01 Jan 1970 00:00:00 GMT",
                        AUTH_COOKIE_NAME
                    );
                    send_redirect(
                        &mut stream,
                        "/",
                        &[("Set-Cookie", cookie_header)],
                    );
                    continue;
                }

                if !authenticated {
                    let html = render_login_page(None);
                    send_http_response(
                        &mut stream,
                        "HTTP/1.1 200 OK",
                        "text/html; charset=utf-8",
                        &html,
                        &[],
                    );
                    continue;
                }

                let status_payload = build_status_response(
                    &job_queue,
                    &attempts_current,
                    &attempts_total,
                    &found_count,
                    &last_found,
                    &runtime_metrics,
                    &out_file,
                );

                let wants_json = path_only == "/json"
                    || path_only == "/api/status"
                    || query_map
                        .get("format")
                        .map(|s| s == "json")
                        .unwrap_or(false);

                if wants_json {
                    let body_json =
                        serde_json::to_string(&status_payload).unwrap_or_else(|_| "{}".to_string());
                    send_http_response(
                        &mut stream,
                        "HTTP/1.1 200 OK",
                        "application/json",
                        &body_json,
                        &[],
                    );
                    continue;
                }

                if path_only == "/api/history" {
                    let history = load_history(&out_file);
                    let body_json =
                        serde_json::to_string(&history).unwrap_or_else(|_| "[]".to_string());
                    send_http_response(
                        &mut stream,
                        "HTTP/1.1 200 OK",
                        "application/json",
                        &body_json,
                        &[],
                    );
                    continue;
                }

                if method == "POST" && path_only == "/jobs" {
                    let form = parse_form_urlencoded(&body);
                    let pattern_result = form
                        .get("pattern")
                        .map(|s| sanitize_pattern(s))
                        .unwrap_or_else(|| Err("Pattern wajib diisi".to_string()));
                    let mode_result = form
                        .get("mode")
                        .map(|s| normalize_mode(s))
                        .unwrap_or_else(|| Ok("prefix".to_string()));
                    let count_result = form
                        .get("count")
                        .map(|s| parse_count(s))
                        .unwrap_or_else(|| Ok(1));

                    if let (Ok(pattern), Ok(mode), Ok(count)) = (
                        pattern_result.clone(),
                        mode_result.clone(),
                        count_result.clone(),
                    ) {
                        enqueue_job(&job_queue, pattern, mode, count);
                        send_redirect(&mut stream, "/", &[]);
                    } else {
                        let error_msg = pattern_result
                            .as_ref()
                            .err()
                            .map(|e| e.clone())
                            .or_else(|| mode_result.as_ref().err().map(|e| e.clone()))
                            .or_else(|| count_result.as_ref().err().map(|e| e.clone()))
                            .unwrap_or_else(|| "Input tidak valid".to_string());
                        let history = load_history(&out_file);
                        let html =
                            render_dashboard_html(&status_payload, &history, Some(&error_msg));
                        send_http_response(
                            &mut stream,
                            "HTTP/1.1 400 Bad Request",
                            "text/html; charset=utf-8",
                            &html,
                            &[],
                        );
                    }
                    continue;
                }

                if method == "POST" && path_only == "/jobs/cancel" {
                    let form = parse_form_urlencoded(&body);
                    let message = if let Some(id_str) = form.get("job_id") {
                        if let Ok(job_id) = id_str.trim().parse::<u64>() {
                            match cancel_job(&job_queue, job_id) {
                                CancelStatus::Active => {
                                    format!("Terminate signal dikirim ke job #{}.", job_id)
                                }
                                CancelStatus::Pending => {
                                    format!("Job #{} dihapus dari antrian.", job_id)
                                }
                                CancelStatus::NotFound => {
                                    format!("Job #{} tidak ditemukan.", job_id)
                                }
                            }
                        } else {
                            "job_id tidak valid.".to_string()
                        }
                    } else {
                        "Parameter job_id wajib.".to_string()
                    };
                    let status_now = build_status_response(
                        &job_queue,
                        &attempts_current,
                        &attempts_total,
                        &found_count,
                        &last_found,
                        &runtime_metrics,
                        &out_file,
                    );
                    let history = load_history(&out_file);
                    let html =
                        render_dashboard_html(&status_now, &history, Some(message.as_str()));
                    send_http_response(
                        &mut stream,
                        "HTTP/1.1 200 OK",
                        "text/html; charset=utf-8",
                        &html,
                        &[],
                    );
                    continue;
                }

                if method == "POST" && path_only == "/history/delete" {
                    let form = parse_form_urlencoded(&body);
                    let message = if let Some(address) = form.get("address") {
                        match delete_history_entry(&out_file, address) {
                            Ok(true) => "History entry dihapus.".to_string(),
                            Ok(false) => "History entry tidak ditemukan.".to_string(),
                            Err(err) => format!("Gagal hapus entry: {}", err),
                        }
                    } else {
                        "Address tidak ditemukan di form.".to_string()
                    };
                    let status_now = build_status_response(
                        &job_queue,
                        &attempts_current,
                        &attempts_total,
                        &found_count,
                        &last_found,
                        &runtime_metrics,
                        &out_file,
                    );
                    let history = load_history(&out_file);
                    let html =
                        render_dashboard_html(&status_now, &history, Some(message.as_str()));
                    send_http_response(
                        &mut stream,
                        "HTTP/1.1 200 OK",
                        "text/html; charset=utf-8",
                        &html,
                        &[],
                    );
                    continue;
                }

                if method == "POST" && path_only == "/history/clear" {
                    let message = match clear_history(&out_file) {
                        Ok(_) => "Seluruh history dihapus.".to_string(),
                        Err(err) => format!("Gagal mengosongkan history: {}", err),
                    };
                    let status_now = build_status_response(
                        &job_queue,
                        &attempts_current,
                        &attempts_total,
                        &found_count,
                        &last_found,
                        &runtime_metrics,
                        &out_file,
                    );
                    let history = load_history(&out_file);
                    let html =
                        render_dashboard_html(&status_now, &history, Some(message.as_str()));
                    send_http_response(
                        &mut stream,
                        "HTTP/1.1 200 OK",
                        "text/html; charset=utf-8",
                        &html,
                        &[],
                    );
                    continue;
                }

                if method == "GET" && path_only == "/" {
                    let history = load_history(&out_file);
                    let html =
                        render_dashboard_html(&status_payload, &history, query_map.get("message").map(|s| s.as_str()));
                    send_http_response(
                        &mut stream,
                        "HTTP/1.1 200 OK",
                        "text/html; charset=utf-8",
                        &html,
                        &[],
                    );
                    continue;
                }

                send_http_response(
                    &mut stream,
                    "HTTP/1.1 404 Not Found",
                    "text/plain",
                    "Not found",
                    &[],
                );
            }
            Err(err) if err.kind() == std::io::ErrorKind::WouldBlock => {
                thread::sleep(Duration::from_millis(120));
            }
            Err(err) => {
                eprintln!("\nMonitor error: {}", err);
                thread::sleep(Duration::from_millis(250));
            }
        }
    }

    Ok(())
}

fn main() {
    let args = Args::parse();
    let out_file = args.out.clone();
    let monitor_port = args.monitor_port;
    let initial_pattern = args.pattern.trim().to_string();
    let initial_mode = args.mode.trim().to_string();
    let initial_count = args.count;

    println!("============================================");
    println!("Vanity Generator (Dashboard Mode)");
    println!("Output file : {}", out_file);
    println!("HTTP Port   : {}", monitor_port);
    println!("Auth code   : {}", AUTH_SECRET);
    println!("============================================");

    let attempts = Arc::new(AtomicI64::new(0));
    let total_attempts = Arc::new(AtomicI64::new(0));
    let found_count = Arc::new(AtomicUsize::new(0));
    let last_found_summary = Arc::new(Mutex::new(None));
    let runtime_metrics = Arc::new(Mutex::new(None));
    let shutdown_flag = Arc::new(AtomicBool::new(false));
    let job_queue: JobQueueHandle = Arc::new((Mutex::new(JobQueueState::new()), Condvar::new()));

    if !initial_pattern.is_empty() {
        match sanitize_pattern(&initial_pattern) {
            Ok(pattern) => {
                let mode = normalize_mode(&initial_mode).unwrap_or_else(|err| {
                    println!("Mode tidak valid ({}), fallback ke prefix.", err);
                    "prefix".to_string()
                });
                enqueue_job(&job_queue, pattern, mode, initial_count);
                println!("Initial job dimasukkan dari argumen CLI.");
            }
            Err(err) => println!("Initial pattern invalid: {}. Menunggu input dari web.", err),
        }
    } else {
        println!("Tidak ada job awal. Submit pattern melalui dashboard.");
    }

    let _worker_handle = {
        let jq = Arc::clone(&job_queue);
        let attempts = Arc::clone(&attempts);
        let totals = Arc::clone(&total_attempts);
        let found = Arc::clone(&found_count);
        let last = Arc::clone(&last_found_summary);
        let runtime = Arc::clone(&runtime_metrics);
        let shutdown = Arc::clone(&shutdown_flag);
        let out_file_worker = out_file.clone();
        thread::spawn(move || {
            worker_loop(
                jq,
                attempts,
                totals,
                found,
                last,
                runtime,
                out_file_worker,
                shutdown,
            );
        })
    };

    let console_job_queue = Arc::clone(&job_queue);
    let console_attempts = Arc::clone(&attempts);
    let console_totals = Arc::clone(&total_attempts);
    let console_found = Arc::clone(&found_count);
    let console_last = Arc::clone(&last_found_summary);
    let console_runtime = Arc::clone(&runtime_metrics);
    let console_shutdown = Arc::clone(&shutdown_flag);
    let out_file_console = out_file.clone();

    thread::spawn(move || loop {
        if console_shutdown.load(Ordering::Relaxed) {
            break;
        }
        let status = build_status_response(
            &console_job_queue,
            &console_attempts,
            &console_totals,
            &console_found,
            &console_last,
            &console_runtime,
            &out_file_console,
        );
        if let Some(job) = &status.current_job {
            print!(
                "\r[RUNNING job #{:>3}] pattern={} attempts={} rate={:.1}/s pending={:<2}",
                job.id,
                job.pattern,
                status.attempts_current,
                status.attempts_per_second,
                status.pending_jobs.len()
            );
        } else {
            print!(
                "\r[IDLE] Pending jobs: {:<3} Last found: {}",
                status.pending_jobs.len(),
                status
                    .last_found
                    .as_ref()
                    .map(|f| f.address.as_str())
                    .unwrap_or("-")
            );
        }
        let _ = std::io::stdout().flush();
        thread::sleep(Duration::from_millis(800));
    });

    let http_job_queue = Arc::clone(&job_queue);
    let http_attempts = Arc::clone(&attempts);
    let http_totals = Arc::clone(&total_attempts);
    let http_found = Arc::clone(&found_count);
    let http_last = Arc::clone(&last_found_summary);
    let http_runtime = Arc::clone(&runtime_metrics);
    let http_shutdown = Arc::clone(&shutdown_flag);
    let out_file_http = out_file.clone();
    let monitor_handle = thread::spawn(move || {
        if let Err(err) = start_http_monitor(
            monitor_port,
            out_file_http,
            http_attempts,
            http_totals,
            http_found,
            http_last,
            http_runtime,
            http_job_queue,
            http_shutdown,
        ) {
            eprintln!("\nHTTP monitor stopped: {}", err);
        }
    });

    let _ = monitor_handle.join();
}
