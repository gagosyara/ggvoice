// Скрываем черное консольное окно при запуске готового .exe
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use anyhow::{anyhow, Result};
use base64::{engine::general_purpose::URL_SAFE_NO_PAD, Engine as _};
use chacha20poly1305::{
    aead::{Aead, KeyInit},
    ChaCha20Poly1305, Nonce,
};
use cpal::traits::{DeviceTrait, HostTrait, StreamTrait};
use cpal::{Device, StreamConfig};
use eframe::egui;
use nnnoiseless::DenoiseState;
use opus::{Application, Channels, Decoder, Encoder};
use rand::RngCore;
use ringbuf::{traits::*, HeapRb};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::ffi::OsStr;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4, UdpSocket};
use std::os::windows::ffi::OsStrExt;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicI32, AtomicU32, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};
use windows_sys::Win32::UI::Input::KeyboardAndMouse::GetAsyncKeyState;
use windows_sys::Win32::UI::Shell::ShellExecuteW;
use windows_sys::Win32::UI::WindowsAndMessaging::{
    FindWindowW, SetForegroundWindow, ShowWindow, SW_RESTORE, SW_SHOW, SW_SHOWNORMAL,
};

// === КОНФИГУРАЦИЯ ПРОЕКТА И GITHUB RELEASES ===
const APP_VERSION: &str = "1.0.2";
const GITHUB_REPO: &str = "gagosyara/ggvoice";
const GITHUB_RELEASES_LATEST_URL: &str = "https://github.com/gagosyara/ggvoice/releases/latest";
const BEACON_URL: &str = "https://ggvoice-beacon.nikiforgagos.workers.dev";
const WINDOW_TITLE: &str = "GGVOICE.EXE";

const SAMPLE_RATE: u32 = 48_000;
const FRAME_SIZE: usize = 480;
const TARGET_RMS: f32 = 0.12;
const MAX_GAIN: f32 = 6.5;
const MIN_GAIN: f32 = 0.85;
const MAX_ROOM_USERS: usize = 20;

// Типы UDP пакетов
const PKT_PING: u8 = 0x01;
const PKT_VOICE: u8 = 0x02;

// Палитра: Deep Black + Hot Neon Pink + Retro Gray
const VOID_BLACK: egui::Color32 = egui::Color32::from_rgb(7, 7, 10);
const PANEL_BLACK: egui::Color32 = egui::Color32::from_rgb(13, 13, 18);
const GRID_LINE: egui::Color32 = egui::Color32::from_rgb(20, 20, 28);
const RETRO_PINK: egui::Color32 = egui::Color32::from_rgb(244, 42, 133);
const RETRO_PINK_DIM: egui::Color32 = egui::Color32::from_rgb(120, 24, 68);
const RETRO_GRAY: egui::Color32 = egui::Color32::from_rgb(150, 153, 165);
const RETRO_BORDER: egui::Color32 = egui::Color32::from_rgb(105, 108, 120);
const CYBER_MINT: egui::Color32 = egui::Color32::from_rgb(45, 226, 150);

#[derive(Clone, Copy)]
enum UiCueKind {
    Join,
    Leave,
}

fn synth_join_samples(sample_rate: u32) -> Vec<f32> {
    let sr = sample_rate.max(8000) as f32;
    let mut samples = Vec::new();
    let mut phase = 0.0_f32;

    let append_smooth_note = |out: &mut Vec<f32>,
                            phase_acc: &mut f32,
                            freq: f32,
                            dur_sec: f32,
                            amp: f32| {
        let total = ((dur_sec * sr).round() as usize).max(1);
        let two_pi = std::f32::consts::TAU;
        let phase_step = two_pi * freq / sr;

        for i in 0..total {
            let p = i as f32 / (total.max(1) as f32);
            let env = 0.5 * (1.0 - (two_pi * p.min(0.5)).cos())
                * if p > 0.5 {
                    0.5 * (1.0 + (std::f32::consts::PI * ((p - 0.5) * 2.0)).cos())
                } else {
                    1.0
                };
            let s = phase_acc.sin() * amp * env;
            *phase_acc = (*phase_acc + phase_step) % two_pi;
            out.push(s);
        }
    };

    let append_silence = |out: &mut Vec<f32>, phase_acc: &mut f32, freq_hold: f32, dur_sec: f32| {
        let total = ((dur_sec * sr).round() as usize).max(1);
        let two_pi = std::f32::consts::TAU;
        let phase_step = two_pi * freq_hold / sr;
        for _ in 0..total {
            *phase_acc = (*phase_acc + phase_step) % two_pi;
            out.push(0.0);
        }
    };

    append_smooth_note(&mut samples, &mut phase, 440.0, 0.075, 0.085);
    append_silence(&mut samples, &mut phase, 440.0, 0.020);
    append_smooth_note(&mut samples, &mut phase, 659.25, 0.115, 0.090);
    samples
}

fn synth_ui_cue(kind: UiCueKind, sample_rate: u32) -> Vec<f32> {
    let mut samples = synth_join_samples(sample_rate);
    if matches!(kind, UiCueKind::Leave) {
        samples.reverse();
    }
    samples
}

fn to_wide_null(s: &str) -> Vec<u16> {
    OsStr::new(s)
        .encode_wide()
        .chain(std::iter::once(0))
        .collect()
}

fn open_url_in_browser(url: &str) {
    unsafe {
        let wide_op = to_wide_null("open");
        let wide_url = to_wide_null(url);
        ShellExecuteW(
            std::ptr::null_mut(),
            wide_op.as_ptr(),
            wide_url.as_ptr(),
            std::ptr::null(),
            std::ptr::null(),
            SW_SHOWNORMAL,
        );
    }
}

fn parse_semver_tuple(ver: &str) -> Option<(u32, u32, u32)> {
    let clean = ver.trim().trim_start_matches(['v', 'V']);
    let core = clean.split(['-', '+']).next()?;
    let mut parts = core.split('.');
    let major = parts.next()?.parse::<u32>().ok()?;
    let minor = parts.next().unwrap_or("0").parse::<u32>().ok()?;
    let patch = parts.next().unwrap_or("0").parse::<u32>().ok()?;
    Some((major, minor, patch))
}

fn is_newer_version(latest_tag: &str, current_ver: &str) -> bool {
    match (parse_semver_tuple(latest_tag), parse_semver_tuple(current_ver)) {
        (Some(lat), Some(cur)) => lat > cur,
        _ => false,
    }
}

fn extract_json_string_field(json: &str, field_name: &str) -> Option<String> {
    let needle = format!("\"{}\":", field_name);
    let idx = json.find(&needle)?;
    let rest = json[idx + needle.len()..].trim_start();
    let rest = rest.strip_prefix('"')?;
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

struct UpdateInfo {
    tag_name: String,
    html_url: String,
}

fn check_github_latest_release() -> Option<UpdateInfo> {
    let api_url = format!("https://api.github.com/repos/{}/releases/latest", GITHUB_REPO);
    let resp = ureq::get(&api_url)
        .timeout(Duration::from_secs(4))
        .set("User-Agent", "GGVoice-Client")
        .set("Accept", "application/vnd.github+json")
        .call()
        .ok()?;
    let body = resp.into_string().ok()?;
    let tag_name = extract_json_string_field(&body, "tag_name")?;
    if !is_newer_version(&tag_name, APP_VERSION) {
        return None;
    }
    let html_url = extract_json_string_field(&body, "html_url")
        .unwrap_or_else(|| GITHUB_RELEASES_LATEST_URL.to_string());
    Some(UpdateInfo { tag_name, html_url })
}

fn focus_existing_window(title: &str) {
    unsafe {
        let wide_title = to_wide_null(title);
        let hwnd = FindWindowW(std::ptr::null(), wide_title.as_ptr());
        if !hwnd.is_null() {
            ShowWindow(hwnd, SW_RESTORE);
            ShowWindow(hwnd, SW_SHOW);
            SetForegroundWindow(hwnd);
        }
    }
}

fn lock_file_path() -> Option<PathBuf> {
    std::env::var_os("APPDATA").map(|dir| PathBuf::from(dir).join("GGVoice").join("ggvoice.lock"))
}

fn release_single_instance_lock() {
    if let Some(path) = lock_file_path() {
        let _ = std::fs::remove_file(path);
    }
}

fn acquire_single_instance_or_focus() -> bool {
    use std::io::Write;
    if let Some(lock_path) = lock_file_path() {
        if let Some(parent) = lock_path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }

        match std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&lock_path)
        {
            Ok(mut file) => {
                let _ = writeln!(file, "pid={}", std::process::id());
                std::mem::forget(file);
                return false;
            }
            Err(_) => {
                focus_existing_window(WINDOW_TITLE);
                let is_fresh_lock = std::fs::metadata(&lock_path)
                    .and_then(|m| m.modified())
                    .ok()
                    .and_then(|t| t.elapsed().ok())
                    .map(|age| age < Duration::from_millis(2500))
                    .unwrap_or(false);

                if is_fresh_lock {
                    return true;
                }

                unsafe {
                    let wide_title = to_wide_null(WINDOW_TITLE);
                    let hwnd = FindWindowW(std::ptr::null(), wide_title.as_ptr());
                    if hwnd.is_null() {
                        let _ = std::fs::remove_file(&lock_path);
                        if let Ok(mut file) = std::fs::OpenOptions::new()
                            .write(true)
                            .create_new(true)
                            .open(&lock_path)
                        {
                            let _ = writeln!(file, "pid={}", std::process::id());
                            std::mem::forget(file);
                            return false;
                        }
                    }
                }
                return true;
            }
        }
    }
    false
}

/// Путь в системном %APPDATA%\GGVoice\prefs.txt (не создает файлов рядом с .exe)
fn prefs_file_path() -> Option<PathBuf> {
    std::env::var_os("APPDATA").map(|dir| PathBuf::from(dir).join("GGVoice").join("prefs.txt"))
}

struct UserPrefs {
    client_id: u64,
    nickname: String,
    room: String,
    password: String,
    ptt_enabled: bool,
    ptt_vk: i32,
    boost_enabled: bool,
    sounds_enabled: bool,
    ns_level: i32,
    mic_device: String,
    out_device: String,
}

fn generate_non_zero_id() -> u64 {
    let mut id = rand::thread_rng().next_u64();
    if id == 0 {
        id = 1;
    }
    id
}

fn load_prefs(fallback_nick: &str) -> UserPrefs {
    let mut prefs = UserPrefs {
        client_id: generate_non_zero_id(),
        nickname: fallback_nick.to_string(),
        room: String::new(),
        password: String::new(),
        ptt_enabled: false,
        ptt_vk: 0x56, // V по умолчанию
        boost_enabled: false,
        sounds_enabled: true,
        ns_level: 6,
        mic_device: String::new(),
        out_device: String::new(),
    };

    if let Some(path) = prefs_file_path() {
        if let Ok(content) = std::fs::read_to_string(path) {
            for line in content.lines() {
                if let Some(val) = line.strip_prefix("id=") {
                    if let Ok(parsed_id) = val.trim().parse::<u64>() {
                        if parsed_id != 0 {
                            prefs.client_id = parsed_id;
                        }
                    }
                } else if let Some(val) = line.strip_prefix("nick=") {
                    let trimmed = val.trim();
                    if !trimmed.is_empty() {
                        prefs.nickname = trimmed.to_string();
                    }
                } else if let Some(val) = line.strip_prefix("room=") {
                    prefs.room = val.trim().to_string();
                } else if let Some(val) = line.strip_prefix("pass=") {
                    prefs.password = val.trim().to_string();
                } else if let Some(val) = line.strip_prefix("ptt=") {
                    prefs.ptt_enabled = val.trim() == "1";
                } else if let Some(val) = line.strip_prefix("ptt_vk=") {
                    if let Ok(vk) = val.trim().parse::<i32>() {
                        if vk > 0 {
                            prefs.ptt_vk = vk;
                        }
                    }
                } else if let Some(val) = line.strip_prefix("boost=") {
                    prefs.boost_enabled = val.trim() == "1";
                } else if let Some(val) = line.strip_prefix("sounds=") {
                    prefs.sounds_enabled = val.trim() == "1";
                } else if let Some(val) = line.strip_prefix("ns=") {
                    if let Ok(n) = val.trim().parse::<i32>() {
                        prefs.ns_level = n.clamp(1, 10);
                    }
                } else if let Some(val) = line.strip_prefix("mic=") {
                    prefs.mic_device = val.trim().to_string();
                } else if let Some(val) = line.strip_prefix("out=") {
                    prefs.out_device = val.trim().to_string();
                }
            }
        }
    }

    prefs
}

fn save_prefs(
    client_id: u64,
    nick: &str,
    room: &str,
    pass: &str,
    ptt_enabled: bool,
    ptt_vk: i32,
    boost_enabled: bool,
    sounds_enabled: bool,
    ns_level: i32,
    mic_device: &str,
    out_device: &str,
) {
    if let Some(path) = prefs_file_path() {
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        let clean_nick = nick.replace(['\r', '\n'], "");
        let clean_room = room.replace(['\r', '\n'], "");
        let clean_pass = pass.replace(['\r', '\n'], "");
        let clean_mic = mic_device.replace(['\r', '\n'], "");
        let clean_out = out_device.replace(['\r', '\n'], "");
        let ptt_flag = if ptt_enabled { "1" } else { "0" };
        let boost_flag = if boost_enabled { "1" } else { "0" };
        let sounds_flag = if sounds_enabled { "1" } else { "0" };
        let clean_ns = ns_level.clamp(1, 10);
        let data = format!(
            "id={}\nnick={}\nroom={}\npass={}\nptt={}\nptt_vk={}\nboost={}\nsounds={}\nns={}\nmic={}\nout={}\n",
            client_id, clean_nick, clean_room, clean_pass, ptt_flag, ptt_vk, boost_flag, sounds_flag, clean_ns, clean_mic, clean_out
        );
        let _ = std::fs::write(path, data);
    }
}

fn is_vk_pressed(vk: i32) -> bool {
    if vk <= 0 {
        return false;
    }
    unsafe { (GetAsyncKeyState(vk) as u16 & 0x8000) != 0 }
}

fn vk_name(vk: i32) -> String {
    match vk {
        0x04 => "СКМ (Mouse3)".to_string(),
        0x05 => "Mouse4 (Бок. 1)".to_string(),
        0x06 => "Mouse5 (Бок. 2)".to_string(),
        0x08 => "Backspace".to_string(),
        0x09 => "Tab".to_string(),
        0x0D => "Enter".to_string(),
        0x10 | 0xA0 | 0xA1 => "Shift".to_string(),
        0x11 | 0xA2 | 0xA3 => "Ctrl".to_string(),
        0x12 | 0xA4 | 0xA5 => "Alt".to_string(),
        0x14 => "CapsLock".to_string(),
        0x20 => "Space".to_string(),
        0xC0 => "~ (Ё)".to_string(),
        0x30..=0x39 => format!("{}", (vk as u8) as char),
        0x41..=0x5A => format!("{}", (vk as u8) as char),
        0x70..=0x7B => format!("F{}", vk - 0x6F),
        _ => format!("KEY_{:02X}", vk),
    }
}

fn poll_any_pressed_vk() -> Option<i32> {
    for vk in [0x04, 0x05, 0x06] {
        if is_vk_pressed(vk) {
            return Some(vk);
        }
    }
    for vk in 0x08..=0xFE {
        if vk == 0x1B || vk == 0x10 || vk == 0x11 || vk == 0x12 {
            continue;
        }
        if is_vk_pressed(vk) {
            return Some(vk);
        }
    }
    None
}

fn generate_gg_icon() -> egui::IconData {
    let size = 64usize;
    let mut rgba = vec![0u8; size * size * 4];

    let glyph_g: [&str; 9] = [
        ".#####.",
        "##...##",
        "##.....",
        "##.....",
        "##.####",
        "##...##",
        "##...##",
        "##...##",
        ".#####.",
    ];

    for y in 0..size {
        for x in 0..size {
            let idx = (y * size + x) * 4;
            let is_outer_border = x < 2 || x >= size - 2 || y < 2 || y >= size - 2;
            if is_outer_border {
                rgba[idx] = 244;
                rgba[idx + 1] = 42;
                rgba[idx + 2] = 133;
                rgba[idx + 3] = 255;
            } else {
                rgba[idx] = 10;
                rgba[idx + 1] = 10;
                rgba[idx + 2] = 14;
                rgba[idx + 3] = 255;
            }
        }
    }

    let draw_g = |rgba: &mut [u8], start_x: usize, start_y: usize, color: [u8; 3]| {
        let scale = 3usize;
        for (row, line) in glyph_g.iter().enumerate() {
            for (col, ch) in line.chars().enumerate() {
                if ch == '#' {
                    for sy in 0..scale {
                        for sx in 0..scale {
                            let px = start_x + col * scale + sx;
                            let py = start_y + row * scale + sy;
                            if px < size && py < size {
                                let idx = (py * size + px) * 4;
                                rgba[idx] = color[0];
                                rgba[idx + 1] = color[1];
                                rgba[idx + 2] = color[2];
                                rgba[idx + 3] = 255;
                            }
                        }
                    }
                }
            }
        }
    };

    draw_g(&mut rgba, 10, 19, [244, 42, 133]);
    draw_g(&mut rgba, 8, 18, [240, 240, 245]);

    draw_g(&mut rgba, 36, 19, [110, 20, 65]);
    draw_g(&mut rgba, 34, 18, [244, 42, 133]);

    egui::IconData {
        rgba,
        width: size as u32,
        height: size as u32,
    }
}

fn derive_room_secrets(room_name: &str, password: &str) -> (String, [u8; 32]) {
    let norm_room = room_name.trim().to_lowercase();
    let norm_pass = password.trim();

    let mut hasher_id = Sha256::new();
    hasher_id.update(b"GGVOICE_ID_V1:");
    hasher_id.update(norm_room.as_bytes());
    hasher_id.update(b":");
    hasher_id.update(norm_pass.as_bytes());
    let id_hash = hasher_id.finalize();
    let room_hash_hex = URL_SAFE_NO_PAD.encode(&id_hash[..16]);

    let mut hasher_key = Sha256::new();
    hasher_key.update(b"GGVOICE_KEY_V1:");
    hasher_key.update(norm_room.as_bytes());
    hasher_key.update(b":");
    hasher_key.update(norm_pass.as_bytes());
    let key_hash = hasher_key.finalize();
    let mut key = [0u8; 32];
    key.copy_from_slice(&key_hash);

    (room_hash_hex, key)
}



struct PeerNode {
    id: u64,
    name: String,
    addr: SocketAddr,
    volume: f32,
    last_seen: Instant,
    last_spoke: Instant,
    connected: bool,
    last_seq: Option<u64>,
    jitter_primed: bool,
    decoder: Decoder,
    audio_queue: Vec<f32>,
}

struct RoomState {
    my_id: u64,
    my_name: Mutex<String>,
    in_room: AtomicBool,
    room_hash: Mutex<String>,
    room_key: Mutex<[u8; 32]>,
    peers: Mutex<HashMap<u64, PeerNode>>,
}

struct SharedState {
    muted: AtomicBool,
    deafened: AtomicBool,
    ptt_enabled: AtomicBool,
    ptt_vk: AtomicI32,
    ptt_active: AtomicBool,
    loopback_enabled: AtomicBool,
    boost_enabled: AtomicBool,
    sounds_enabled: AtomicBool,
    ui_cue_queue: Mutex<Vec<f32>>,
    my_level_bits: AtomicU32,
    my_speaking: AtomicBool,
    status_text: Mutex<String>,
    public_addr: Mutex<SocketAddr>,
    ns_level: AtomicI32, // 1..10 noise suppression strictness (default 5)
    room: RoomState,
}

impl SharedState {
    fn new(
        client_id: u64,
        public_addr: SocketAddr,
        initial_nick: String,
        ptt_enabled: bool,
        ptt_vk: i32,
        boost_enabled: bool,
        sounds_enabled: bool,
    ) -> Self {
        Self {
            muted: AtomicBool::new(false),
            deafened: AtomicBool::new(false),
            ptt_enabled: AtomicBool::new(ptt_enabled),
            ptt_vk: AtomicI32::new(ptt_vk),
            ptt_active: AtomicBool::new(false),
            loopback_enabled: AtomicBool::new(false),
            boost_enabled: AtomicBool::new(boost_enabled),
            sounds_enabled: AtomicBool::new(sounds_enabled),
            ui_cue_queue: Mutex::new(Vec::new()),
            my_level_bits: AtomicU32::new(0.0_f32.to_bits()),
            my_speaking: AtomicBool::new(false),
            status_text: Mutex::new("Offline".to_string()),
            public_addr: Mutex::new(public_addr),
            ns_level: AtomicI32::new(5),
            room: RoomState {
                my_id: client_id,
                my_name: Mutex::new(initial_nick),
                in_room: AtomicBool::new(false),
                room_hash: Mutex::new(String::new()),
                room_key: Mutex::new([0u8; 32]),
                peers: Mutex::new(HashMap::new()),
            },
        }
    }

    fn my_level(&self) -> f32 {
        f32::from_bits(self.my_level_bits.load(Ordering::Relaxed))
    }

    fn set_my_level(&self, lvl: f32) {
        self.my_level_bits.store(lvl.to_bits(), Ordering::Relaxed);
    }

    fn play_cue(&self, kind: UiCueKind, force: bool) {
        if !force && !self.sounds_enabled.load(Ordering::Relaxed) {
            return;
        }
        let samples = synth_ui_cue(kind, SAMPLE_RATE);
        if let Ok(mut q) = self.ui_cue_queue.lock() {
            q.extend_from_slice(&samples);
            if q.len() > (SAMPLE_RATE as usize) * 2 {
                let excess = q.len() - (SAMPLE_RATE as usize) * 2;
                q.drain(0..excess);
            }
        }
    }
}

fn discover_public_addr(socket: &UdpSocket) -> Result<SocketAddr> {
    let stun_server = "stun.l.google.com:19302";
    socket.set_read_timeout(Some(Duration::from_secs(2)))?;

    let mut req = [0u8; 20];
    req[0..2].copy_from_slice(&0x0001u16.to_be_bytes());
    req[2..4].copy_from_slice(&0x0000u16.to_be_bytes());
    req[4..8].copy_from_slice(&0x2112A442u32.to_be_bytes());
    rand::thread_rng().fill_bytes(&mut req[8..20]);

    socket.send_to(&req, stun_server)?;

    let mut buf = [0u8; 512];
    let (len, _) = socket.recv_from(&mut buf)?;
    if len < 20 {
        return Err(anyhow!("Short STUN response"));
    }

    let mut pos = 20;
    while pos + 4 <= len {
        let attr_type = u16::from_be_bytes([buf[pos], buf[pos + 1]]);
        let attr_len = u16::from_be_bytes([buf[pos + 2], buf[pos + 3]]) as usize;
        pos += 4;

        if attr_type == 0x0020 && attr_len >= 8 && pos + attr_len <= len {
            if buf[pos + 1] == 0x01 {
                let port = u16::from_be_bytes([buf[pos + 2], buf[pos + 3]]) ^ 0x2112;
                let xip =
                    u32::from_be_bytes([buf[pos + 4], buf[pos + 5], buf[pos + 6], buf[pos + 7]]);
                let ip = Ipv4Addr::from(xip ^ 0x2112A442);
                return Ok(SocketAddr::V4(SocketAddrV4::new(ip, port)));
            }
        }
        pos += (attr_len + 3) & !3;
    }

    Err(anyhow!("No XOR-MAPPED-ADDRESS"))
}

fn encrypt_addr_blob(addr: SocketAddr, key: &[u8; 32]) -> String {
    let mut raw = [0u8; 6];
    if let SocketAddr::V4(v4) = addr {
        raw[0..4].copy_from_slice(&v4.ip().octets());
        raw[4..6].copy_from_slice(&v4.port().to_be_bytes());
    }
    let mut nonce_bytes = [0u8; 12];
    rand::thread_rng().fill_bytes(&mut nonce_bytes);
    let nonce = Nonce::from_slice(&nonce_bytes);
    let cipher = ChaCha20Poly1305::new(key.into());
    let ct = cipher.encrypt(nonce, raw.as_ref()).unwrap_or_default();

    let mut out = Vec::with_capacity(12 + ct.len());
    out.extend_from_slice(&nonce_bytes);
    out.extend_from_slice(&ct);
    URL_SAFE_NO_PAD.encode(&out)
}

fn decrypt_addr_blob(blob: &str, key: &[u8; 32]) -> Result<SocketAddr> {
    let data = URL_SAFE_NO_PAD.decode(blob)?;
    if data.len() < 12 + 6 {
        return Err(anyhow!("Invalid blob"));
    }
    let nonce = Nonce::from_slice(&data[..12]);
    let cipher = ChaCha20Poly1305::new(key.into());
    let pt = cipher
        .decrypt(nonce, &data[12..])
        .map_err(|_| anyhow!("Wrong password"))?;
    if pt.len() != 6 {
        return Err(anyhow!("Bad addr len"));
    }
    let ip = Ipv4Addr::new(pt[0], pt[1], pt[2], pt[3]);
    let port = u16::from_be_bytes([pt[4], pt[5]]);
    Ok(SocketAddr::V4(SocketAddrV4::new(ip, port)))
}

fn parse_mesh_peers(json: &str) -> Vec<(u64, String)> {
    let mut result = Vec::new();
    let mut search_pos = 0;

    while let Some(blob_idx) = json[search_pos..].find("\"blob\":\"") {
        let abs_blob_key = search_pos + blob_idx;
        let val_start = abs_blob_key + 8;
        if let Some(val_end_rel) = json[val_start..].find('"') {
            let blob = json[val_start..val_start + val_end_rel].to_string();

            let prefix = &json[..abs_blob_key];
            if let Some(colon_pos) = prefix.rfind("\":{") {
                if let Some(quote_start) = prefix[..colon_pos].rfind('"') {
                    let id_str = &prefix[quote_start + 1..colon_pos];
                    if let Ok(pid) = id_str.parse::<u64>() {
                        result.push((pid, blob));
                    }
                }
            }
            search_pos = val_start + val_end_rel + 1;
        } else {
            break;
        }
    }

    result
}

/// Регистрирует себя при входе в комнату (с авто-повтором и fallback на GET)
fn beacon_sync_mesh(room_hash: &str, my_id: u64, my_blob: &str) -> Result<Vec<(u64, String)>> {
    let url = format!("{}/?room={}", BEACON_URL.trim_end_matches('/'), room_hash);
    let payload = format!("{{\"id\":\"{}\",\"blob\":\"{}\"}}", my_id, my_blob);
    let mut last_err = anyhow!("Unknown error");

    for _ in 0..2 {
        match ureq::post(&url)
            .timeout(Duration::from_secs(3))
            .set("Content-Type", "application/json")
            .send_string(&payload)
        {
            Ok(resp) => {
                let text = resp.into_string()?;
                return Ok(parse_mesh_peers(&text));
            }
            Err(e) => {
                last_err = anyhow!("Beacon err: {}", e);
                thread::sleep(Duration::from_millis(200));
            }
        }
    }

    if let Ok(peers) = beacon_fetch_mesh(room_hash) {
        return Ok(peers);
    }

    Err(last_err)
}

/// Читает список участников в фоне через GET
fn beacon_fetch_mesh(room_hash: &str) -> Result<Vec<(u64, String)>> {
    let url = format!("{}/?room={}", BEACON_URL.trim_end_matches('/'), room_hash);
    let text = ureq::get(&url)
        .timeout(Duration::from_secs(3))
        .call()?
        .into_string()?;
    Ok(parse_mesh_peers(&text))
}

fn beacon_leave_mesh(room_hash: &str, my_id: u64) {
    let url = format!(
        "{}/?room={}&id={}",
        BEACON_URL.trim_end_matches('/'),
        room_hash,
        my_id
    );
    let _ = ureq::delete(&url).timeout(Duration::from_secs(2)).call();
}

struct Bullet {
    x: f32, // 0.0..1.0 внутри экрана монитора
    y: f32, // 0.0..1.0 (1.0 = низ, 0.0 = верх)
}

struct MiniGameAnim {
    plane_x: f32,
    bullets: Vec<Bullet>,
    enemies_alive: [[bool; 6]; 2],
    enemy_dir: f32,
    enemy_offset_x: f32,
    shoot_cooldown: f32,
    score: u32,
    last_tick: Instant,
}

impl Default for MiniGameAnim {
    fn default() -> Self {
        Self {
            plane_x: 0.5,
            bullets: Vec::new(),
            enemies_alive: [[true; 6]; 2],
            enemy_dir: 1.0,
            enemy_offset_x: 0.0,
            shoot_cooldown: 0.25,
            score: 720,
            last_tick: Instant::now(),
        }
    }
}

impl MiniGameAnim {
    fn update(&mut self) {
        let now = Instant::now();
        let dt = now.duration_since(self.last_tick).as_secs_f32().min(0.05);
        self.last_tick = now;

        let t = now.elapsed().as_secs_f32();
        self.plane_x = (0.5 + 0.34 * (t * 1.4).sin()).clamp(0.14, 0.86);

        self.enemy_offset_x += self.enemy_dir * dt * 0.14;
        if self.enemy_offset_x > 0.10 {
            self.enemy_offset_x = 0.10;
            self.enemy_dir = -1.0;
        } else if self.enemy_offset_x < -0.10 {
            self.enemy_offset_x = -0.10;
            self.enemy_dir = 1.0;
        }

        self.shoot_cooldown -= dt;
        if self.shoot_cooldown <= 0.0 {
            self.shoot_cooldown = 0.34;
            self.bullets.push(Bullet {
                x: self.plane_x,
                y: 0.78,
            });
        }

        for b in &mut self.bullets {
            b.y -= dt * 1.15;
        }

        let mut any_alive = false;
        for row in 0..2 {
            for col in 0..6 {
                if !self.enemies_alive[row][col] {
                    continue;
                }
                any_alive = true;
                let ex = 0.18 + (col as f32) * 0.128 + self.enemy_offset_x;
                let ey = 0.30 + (row as f32) * 0.15;

                for b in &mut self.bullets {
                    if b.y > 0.0 && (b.x - ex).abs() < 0.055 && (b.y - ey).abs() < 0.07 {
                        self.enemies_alive[row][col] = false;
                        b.y = -1.0;
                        self.score += 10;
                        break;
                    }
                }
            }
        }

        self.bullets.retain(|b| b.y > -0.1);

        if !any_alive {
            self.enemies_alive = [[true; 6]; 2];
        }
    }

    fn draw(&mut self, ui: &mut egui::Ui, desk_tex: Option<&egui::TextureHandle>) {
        self.update();

        let avail = ui.available_size();
        let box_w = avail.x.max(120.0);
        let box_h = avail.y.max(120.0);
        let (outer_rect, _) =
            ui.allocate_exact_size(egui::vec2(box_w, box_h), egui::Sense::hover());
        let painter = ui.painter();

        let frame_rect = outer_rect.shrink2(egui::vec2(2.0, 2.0));

        // Вписываем картинку окружения без перекрытия сетки снаружи
        let scene_rect = if let Some(tex) = desk_tex {
            let tex_sz = tex.size_vec2().max(egui::vec2(1.0, 1.0));
            let inner = frame_rect.shrink2(egui::vec2(4.0, 4.0));
            let scale = (inner.width() / tex_sz.x)
                .min(inner.height() / tex_sz.y)
                .max(0.1);
            let draw_sz = tex_sz * scale;
            let rect = egui::Rect::from_center_size(inner.center(), draw_sz);

            painter.image(
                tex.id(),
                rect,
                egui::Rect::from_min_max(egui::pos2(0.0, 0.0), egui::pos2(1.0, 1.0)),
                egui::Color32::WHITE,
            );
            rect
        } else {
            frame_rect.shrink2(egui::vec2(8.0, 8.0))
        };

        // Относительные координаты экрана монитора внутри картинки desk_scene.png
        let scr_x_min = 0.295_f32;
        let scr_x_max = 0.714_f32;
        let scr_y_min = 0.115_f32;
        let scr_y_max = 0.625_f32;

        let scr_rect = egui::Rect::from_min_max(
            egui::pos2(
                scene_rect.left() + scene_rect.width() * scr_x_min,
                scene_rect.top() + scene_rect.height() * scr_y_min,
            ),
            egui::pos2(
                scene_rect.left() + scene_rect.width() * scr_x_max,
                scene_rect.top() + scene_rect.height() * scr_y_max,
            ),
        );

        // Фон внутри экрана монитора поверх анимации
        painter.rect_filled(scr_rect, 0.0, VOID_BLACK);

        // Адаптивный масштаб относительно ширины экрана монитора
        let ui_scale = (scr_rect.width() / 520.0_f32).clamp(0.28_f32, 1.35_f32);
        let pad_x = 7.0_f32 * ui_scale;
        let pad_y = 5.0_f32 * ui_scale;

        // HUD внутри мини-игры с пропорциональным масштабированием
        let font_size = (11.0_f32 * ui_scale).clamp(5.0_f32, 16.0_f32);
        let hud_font = egui::FontId::monospace(font_size);

        painter.text(
            scr_rect.left_top() + egui::vec2(pad_x, pad_y),
            egui::Align2::LEFT_TOP,
            format!("SCORE {:06}", self.score),
            hud_font.clone(),
            egui::Color32::WHITE,
        );

        let lives_galley = painter.layout_no_wrap(
            "LIVES".to_string(),
            hud_font,
            egui::Color32::WHITE,
        );
        let h_px = (1.35_f32 * ui_scale).max(0.65_f32);
        let heart_w = 7.0_f32 * h_px;
        let heart_gap = 2.5_f32 * h_px;
        let hearts_total_w = 3.0_f32 * heart_w + 2.0_f32 * heart_gap;
        let label_gap = 4.0_f32 * ui_scale;

        let lives_x = scr_rect.right() - pad_x - hearts_total_w - label_gap - lives_galley.size().x;
        let lives_y = scr_rect.top() + pad_y;
        painter.galley(egui::pos2(lives_x, lives_y), lives_galley, egui::Color32::WHITE);

        let heart_pattern: [&str; 6] = [
            ".##.##.",
            "#######",
            "#######",
            ".#####.",
            "..###..",
            "...#...",
        ];
        let hearts_start_x = scr_rect.right() - pad_x - hearts_total_w;
        let hearts_start_y = scr_rect.top() + pad_y + 1.2_f32 * ui_scale;
        for h_idx in 0..3 {
            let ox = hearts_start_x + (h_idx as f32) * (heart_w + heart_gap);
            for (r, row_str) in heart_pattern.iter().enumerate() {
                for (c, ch) in row_str.chars().enumerate() {
                    if ch == '#' {
                        let col = if r == 1 && c == 1 {
                            egui::Color32::from_rgb(255, 175, 215)
                        } else {
                            RETRO_PINK
                        };
                        painter.rect_filled(
                            egui::Rect::from_min_size(
                                egui::pos2(ox + (c as f32) * h_px, hearts_start_y + (r as f32) * h_px),
                                egui::vec2(h_px, h_px),
                            ),
                            0.0,
                            col,
                        );
                    }
                }
            }
        }

        // Звёздочки
        let t = Instant::now().elapsed().as_secs_f32();
        let star_sz = (2.0_f32 * ui_scale).clamp(1.0_f32, 3.0_f32);
        let top_hud_clear = 18.0_f32 * ui_scale + 4.0_f32;
        for i in 0..10u32 {
            let fi = i as f32;
            let sx = scr_rect.left()
                + ((fi * 53.0_f32 + t * 7.0_f32) % (scr_rect.width() - 8.0_f32).max(8.0_f32))
                + 4.0_f32;
            let sy = scr_rect.top()
                + top_hud_clear
                + ((fi * 29.0_f32) % (scr_rect.height() - top_hud_clear - 10.0_f32).max(8.0_f32));
            let star_col = if i % 3 == 0 {
                CYBER_MINT
            } else if i % 3 == 1 {
                RETRO_PINK
            } else {
                RETRO_GRAY
            };
            painter.rect_filled(
                egui::Rect::from_min_size(egui::pos2(sx, sy), egui::vec2(star_sz, star_sz)),
                0.0,
                star_col,
            );
        }

        // Пиксельные враги
        let e_w = (12.0_f32 * ui_scale).clamp(4.0_f32, 16.0_f32);
        let e_h = (7.0_f32 * ui_scale).clamp(2.5_f32, 10.0_f32);
        for row in 0..2 {
            for col in 0..6 {
                if !self.enemies_alive[row][col] {
                    continue;
                }
                let ex = 0.18_f32 + (col as f32) * 0.128_f32 + self.enemy_offset_x;
                let ey = 0.28_f32 + (row as f32) * 0.14_f32;
                let cx = scr_rect.left() + ex * scr_rect.width();
                let cy = scr_rect.top() + ey * scr_rect.height();

                let e_rect =
                    egui::Rect::from_center_size(egui::pos2(cx, cy), egui::vec2(e_w, e_h));
                let col_px = if row == 0 { RETRO_PINK } else { CYBER_MINT };
                painter.rect_filled(e_rect, 0.0, col_px);
            }
        }

        // Пули самолётика
        let b_w = (4.0_f32 * ui_scale).clamp(1.5_f32, 6.0_f32);
        let b_h = (8.0_f32 * ui_scale).clamp(3.0_f32, 12.0_f32);
        for b in &self.bullets {
            if b.y >= 0.0 {
                let bx = scr_rect.left() + b.x * scr_rect.width();
                let by = scr_rect.top() + b.y * scr_rect.height();
                painter.rect_filled(
                    egui::Rect::from_center_size(egui::pos2(bx, by), egui::vec2(b_w, b_h)),
                    0.0,
                    RETRO_PINK,
                );
                painter.rect_filled(
                    egui::Rect::from_center_size(
                        egui::pos2(bx, by - b_h * 0.12_f32),
                        egui::vec2(b_w * 0.5_f32, b_h * 0.65_f32),
                    ),
                    0.0,
                    egui::Color32::WHITE,
                );
            }
        }

        // Детализированный пиксельный истребитель
        let ship_sprite: [&str; 17] = [
            "........P........",
            ".......PWP.......",
            ".......PWP.......",
            "......PWWWP......",
            "......PWMWP......",
            ".....PWCCCWP.....",
            ".....PWCBCWP.....",
            "....PWWCCCWWP....",
            "....PWWCCCWWP....",
            "...PMWWSSSWWMP...",
            "..PPMWWSSSWWMPP..",
            ".PPWMWWSSSWWWMPP.",
            "PPWWMWWSSSWWWMWWP",
            "PWWP.PWWPWWP.PWWP",
            "PP...PWP.PWP...PP",
            ".....PPP.PPP.....",
            "......P...P......",
        ];

        let px = scr_rect.left() + self.plane_x * scr_rect.width();
        let py = scr_rect.top() + 0.80_f32 * scr_rect.height();
        let pix = (2.1_f32 * ui_scale).clamp(0.75_f32, 3.0_f32);
        let sprite_w = 17.0_f32 * pix;
        let sprite_h = 17.0_f32 * pix;
        let start_x = px - sprite_w * 0.5_f32;
        let start_y = py - sprite_h * 0.5_f32;

        let light_pink = egui::Color32::from_rgb(255, 130, 195);
        let soft_gray = egui::Color32::from_rgb(195, 200, 215);
        let cockpit_dark = egui::Color32::from_rgb(38, 44, 78);
        let cockpit_glint = egui::Color32::from_rgb(135, 185, 245);

        for (r, row_str) in ship_sprite.iter().enumerate() {
            for (c, ch) in row_str.chars().enumerate() {
                let color = match ch {
                    'P' => Some(RETRO_PINK),
                    'W' => Some(egui::Color32::WHITE),
                    'S' => Some(soft_gray),
                    'C' => Some(cockpit_dark),
                    'B' => Some(cockpit_glint),
                    'M' => Some(light_pink),
                    _ => None,
                };
                if let Some(col) = color {
                    painter.rect_filled(
                        egui::Rect::from_min_size(
                            egui::pos2(start_x + (c as f32) * pix, start_y + (r as f32) * pix),
                            egui::vec2(pix, pix),
                        ),
                        0.0,
                        col,
                    );
                }
            }
        }

        // Анимированный реактивный выхлоп из двух сопел
        let flame_phase = ((t * 20.0_f32) as i32) % 2 == 0;
        let flame_len = (if flame_phase { 6.0_f32 } else { 4.0_f32 }) * ui_scale;
        for nozzle_col in [6.0_f32, 10.0_f32] {
            let nx = start_x + nozzle_col * pix;
            let ny = start_y + 16.0_f32 * pix;
            painter.rect_filled(
                egui::Rect::from_min_size(egui::pos2(nx, ny), egui::vec2(pix, flame_len)),
                0.0,
                RETRO_PINK,
            );
            painter.rect_filled(
                egui::Rect::from_min_size(egui::pos2(nx, ny), egui::vec2(pix, flame_len * 0.5_f32)),
                0.0,
                egui::Color32::WHITE,
            );
        }
    }
}

fn list_input_devices(host: &cpal::Host) -> Vec<String> {
    let mut names = Vec::new();
    if let Ok(devs) = host.input_devices() {
        for d in devs {
            if let Ok(name) = d.name() {
                if !names.contains(&name) {
                    names.push(name);
                }
            }
        }
    }
    if names.is_empty() {
        if let Some(d) = host.default_input_device() {
            if let Ok(name) = d.name() {
                names.push(name);
            }
        }
    }
    names
}

fn list_output_devices(host: &cpal::Host) -> Vec<String> {
    let mut names = Vec::new();
    if let Ok(devs) = host.output_devices() {
        for d in devs {
            if let Ok(name) = d.name() {
                if !names.contains(&name) {
                    names.push(name);
                }
            }
        }
    }
    if names.is_empty() {
        if let Some(d) = host.default_output_device() {
            if let Ok(name) = d.name() {
                names.push(name);
            }
        }
    }
    names
}

fn find_input_device(host: &cpal::Host, desired_name: &str) -> Result<Device> {
    if !desired_name.is_empty() {
        if let Ok(mut devs) = host.input_devices() {
            if let Some(found) = devs.find(|d| d.name().ok().as_deref() == Some(desired_name)) {
                return Ok(found);
            }
        }
    }
    host.default_input_device()
        .ok_or_else(|| anyhow!("Mic not found"))
}

fn find_output_device(host: &cpal::Host, desired_name: &str) -> Result<Device> {
    if !desired_name.is_empty() {
        if let Ok(mut devs) = host.output_devices() {
            if let Some(found) = devs.find(|d| d.name().ok().as_deref() == Some(desired_name)) {
                return Ok(found);
            }
        }
    }
    host.default_output_device()
        .ok_or_else(|| anyhow!("Output not found"))
}

/// Создаём lock-free поток ввода (никаких мьютексов в аудио-коллбэке)
fn build_input_stream_for_device(
    device: &Device,
    mut prod_in: ringbuf::HeapProd<f32>,
    in_error_flag: Arc<AtomicBool>,
    in_heartbeat_ms: Arc<AtomicU32>,
    start_instant: Instant,
) -> Result<(cpal::Stream, String)> {
    let dev_name = device.name().unwrap_or_else(|_| "MIC".into());
    let default_in_cfg = device.default_input_config()?;
    let in_channels = default_in_cfg.channels() as usize;

    let in_stream_cfg = StreamConfig {
        channels: default_in_cfg.channels(),
        sample_rate: cpal::SampleRate(SAMPLE_RATE),
        buffer_size: cpal::BufferSize::Default,
    };

    let err_flag_cb = in_error_flag.clone();
    let stream = device.build_input_stream(
        &in_stream_cfg,
        move |data: &[f32], _: &cpal::InputCallbackInfo| {
            let now_ms = start_instant.elapsed().as_millis() as u32;
            in_heartbeat_ms.store(now_ms, Ordering::Relaxed);
            for frame in data.chunks(in_channels) {
                let _ = prod_in.try_push(frame[0]);
            }
        },
        move |_| {
            err_flag_cb.store(true, Ordering::Relaxed);
        },
        None,
    )?;
    stream.play()?;
    Ok((stream, dev_name))
}

/// Создаём lock-free поток вывода (никаких мьютексов в аудио-коллбэке)
fn build_output_stream_for_device(
    device: &Device,
    state: Arc<SharedState>,
    mut cons_out: ringbuf::HeapCons<f32>,
    mut cons_lb: ringbuf::HeapCons<f32>,
    out_error_flag: Arc<AtomicBool>,
) -> Result<(cpal::Stream, String)> {
    let dev_name = device.name().unwrap_or_else(|_| "OUT".into());
    let default_out_cfg = device.default_output_config()?;
    let out_channels = default_out_cfg.channels() as usize;

    let out_stream_cfg = StreamConfig {
        channels: default_out_cfg.channels(),
        sample_rate: cpal::SampleRate(SAMPLE_RATE),
        buffer_size: cpal::BufferSize::Default,
    };

    let stream = device.build_output_stream(
        &out_stream_cfg,
        move |data: &mut [f32], _: &cpal::OutputCallbackInfo| {
            let deaf = state.deafened.load(Ordering::Relaxed);
            let lb_on = state.loopback_enabled.load(Ordering::Relaxed);

            let has_net = cons_out.occupied_len() >= FRAME_SIZE * 2;
            let has_lb = lb_on && cons_lb.occupied_len() >= FRAME_SIZE;

            if !lb_on {
                while cons_lb.try_pop().is_some() {}
            }

            let mut cue_samples = Vec::new();
            if let Ok(mut q) = state.ui_cue_queue.try_lock() {
                if !q.is_empty() {
                    let take_n = q.len().min(data.len() / out_channels.max(1));
                    cue_samples.extend(q.drain(0..take_n));
                }
            }
            let mut cue_idx = 0usize;

            for frame in data.chunks_mut(out_channels) {
                let net_s = if has_net {
                    cons_out.try_pop().unwrap_or(0.0)
                } else {
                    0.0
                };
                let lb_s = if has_lb {
                    cons_lb.try_pop().unwrap_or(0.0)
                } else {
                    0.0
                };
                let cue_s = if cue_idx < cue_samples.len() {
                    let v = cue_samples[cue_idx];
                    cue_idx += 1;
                    v
                } else {
                    0.0
                };

                let mixed = if deaf {
                    cue_s.clamp(-0.99, 0.99)
                } else {
                    (net_s + lb_s + cue_s).clamp(-0.99, 0.99)
                };

                for ch in frame.iter_mut() {
                    *ch = mixed;
                }
            }
        },
        move |_| {
            out_error_flag.store(true, Ordering::Relaxed);
        },
        None,
    )?;
    stream.play()?;
    Ok((stream, dev_name))
}

fn compact_device_label(name: &str, max_chars: usize) -> String {
    let cleaned = name
        .replace("Microphone (", "")
        .replace("Микрофон (", "")
        .replace("Динамики (", "")
        .replace("Speakers (", "")
        .replace("Headphones (", "")
        .replace("Наушники (", "")
        .trim_end_matches(')')
        .trim()
        .to_string();

    let source = if cleaned.is_empty() { name } else { &cleaned };
    let chars: Vec<char> = source.chars().collect();
    if chars.len() <= max_chars {
        source.to_string()
    } else {
        let mut out: String = chars[..max_chars.saturating_sub(1)].iter().collect();
        out.push('…');
        out
    }
}

struct GGVoiceApp {
    state: Arc<SharedState>,
    client_id: u64,
    room_input: String,
    pass_input: String,
    nickname_input: String,
    joining_in_progress: Arc<AtomicBool>,
    binding_ptt_key: bool,
    mic_name: String,
    out_name: String,
    available_mics: Vec<String>,
    available_outs: Vec<String>,
    last_device_scan: Instant,
    cons_in_shared: Arc<Mutex<ringbuf::HeapCons<f32>>>,
    prod_out_shared: Arc<Mutex<ringbuf::HeapProd<f32>>>,
    prod_lb_shared: Arc<Mutex<ringbuf::HeapProd<f32>>>,
    available_update: Arc<Mutex<Option<UpdateInfo>>>,
    desk_texture: Option<egui::TextureHandle>,
    welcome_game: MiniGameAnim,
    audio_epoch: Instant,
    in_error_flag: Arc<AtomicBool>,
    in_heartbeat_ms: Arc<AtomicU32>,
    out_error_flag: Arc<AtomicBool>,
    last_audio_recovery: Instant,
    input_stream: Option<cpal::Stream>,
    output_stream: Option<cpal::Stream>,
}

impl GGVoiceApp {
    fn new(cc: &eframe::CreationContext<'_>) -> Self {
        let mut fonts = egui::FontDefinitions::default();
        if let Ok(font_data) = std::fs::read("C:\\Windows\\Fonts\\lucon.ttf") {
            fonts.font_data.insert(
                "lucida_console".to_owned(),
                egui::FontData::from_owned(font_data),
            );
            fonts
                .families
                .entry(egui::FontFamily::Proportional)
                .or_default()
                .insert(0, "lucida_console".to_owned());
            fonts
                .families
                .entry(egui::FontFamily::Monospace)
                .or_default()
                .insert(0, "lucida_console".to_owned());
        }
        cc.egui_ctx.set_fonts(fonts);

        let mut visuals = egui::Visuals::dark();
        visuals.panel_fill = VOID_BLACK;
        visuals.window_fill = VOID_BLACK;
        visuals.extreme_bg_color = VOID_BLACK;
        visuals.window_rounding = egui::Rounding::ZERO;

        visuals.widgets.noninteractive.bg_fill = PANEL_BLACK;
        visuals.widgets.noninteractive.fg_stroke =
            egui::Stroke::new(1.0_f32, egui::Color32::WHITE);
        visuals.widgets.noninteractive.bg_stroke = egui::Stroke::new(1.0_f32, RETRO_BORDER);
        visuals.widgets.noninteractive.rounding = egui::Rounding::ZERO;

        visuals.widgets.inactive.bg_fill = PANEL_BLACK;
        visuals.widgets.inactive.fg_stroke = egui::Stroke::new(1.0_f32, egui::Color32::WHITE);
        visuals.widgets.inactive.bg_stroke = egui::Stroke::new(1.0_f32, RETRO_BORDER);
        visuals.widgets.inactive.rounding = egui::Rounding::ZERO;

        visuals.widgets.hovered.bg_fill = egui::Color32::from_rgb(35, 14, 26);
        visuals.widgets.hovered.fg_stroke = egui::Stroke::new(1.0_f32, egui::Color32::WHITE);
        visuals.widgets.hovered.bg_stroke = egui::Stroke::new(1.0_f32, RETRO_PINK);
        visuals.widgets.hovered.rounding = egui::Rounding::ZERO;

        visuals.widgets.active.bg_fill = RETRO_PINK;
        visuals.widgets.active.fg_stroke = egui::Stroke::new(1.0_f32, VOID_BLACK);
        visuals.widgets.active.rounding = egui::Rounding::ZERO;

        visuals.selection.bg_fill = RETRO_PINK;
        visuals.selection.stroke = egui::Stroke::new(1.0_f32, VOID_BLACK);

        cc.egui_ctx.set_visuals(visuals);

        let desk_texture = image::load_from_memory(include_bytes!("../desk_scene.png"))
            .ok()
            .map(|img| {
                let rgba = img.to_rgba8();
                let size = [rgba.width() as usize, rgba.height() as usize];
                let color_img = egui::ColorImage::from_rgba_unmultiplied(size, rgba.as_raw());
                cc.egui_ctx.load_texture(
                    "desk_scene_tex",
                    color_img,
                    egui::TextureOptions::NEAREST,
                )
            });

        let socket = UdpSocket::bind("0.0.0.0:0").expect("UDP bind failed");
        let local_port = socket.local_addr().unwrap().port();
        let public_addr = discover_public_addr(&socket).unwrap_or_else(|_| {
            SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::LOCALHOST, local_port))
        });

        let random_num = rand::thread_rng().next_u64() % 10000;
        let fallback_nick = format!("Player_{:04}", random_num);
        let prefs = load_prefs(&fallback_nick);

        let state = Arc::new(SharedState::new(
            prefs.client_id,
            public_addr,
            prefs.nickname.clone(),
            prefs.ptt_enabled,
            prefs.ptt_vk,
            prefs.boost_enabled,
            prefs.sounds_enabled,
        ));
        state.ns_level.store(prefs.ns_level.clamp(1, 10), Ordering::Relaxed);

        socket.set_nonblocking(true).unwrap();
        let socket_tx = socket.try_clone().unwrap();
        let socket_rx = socket;

        let host = cpal::default_host();
        let available_mics = list_input_devices(&host);
        let available_outs = list_output_devices(&host);

        let (prod_in, cons_in_raw) = HeapRb::<f32>::new(FRAME_SIZE * 24).split();
        let (prod_out_raw, cons_out) = HeapRb::<f32>::new(FRAME_SIZE * 28).split();
        let (prod_lb_raw, cons_lb) = HeapRb::<f32>::new(FRAME_SIZE * 16).split();

        let cons_in_shared = Arc::new(Mutex::new(cons_in_raw));
        let prod_out_shared = Arc::new(Mutex::new(prod_out_raw));
        let prod_lb_shared = Arc::new(Mutex::new(prod_lb_raw));

        let audio_epoch = Instant::now();
        let in_error_flag = Arc::new(AtomicBool::new(false));
        let in_heartbeat_ms = Arc::new(AtomicU32::new(0));
        let out_error_flag = Arc::new(AtomicBool::new(false));

        let input_device = find_input_device(&host, &prefs.mic_device).expect("Mic not found");
        let (input_stream, mic_name) = build_input_stream_for_device(
            &input_device,
            prod_in,
            in_error_flag.clone(),
            in_heartbeat_ms.clone(),
            audio_epoch,
        )
        .unwrap();

        let output_device =
            find_output_device(&host, &prefs.out_device).expect("Headphones not found");
        let (output_stream, out_name) = build_output_stream_for_device(
            &output_device,
            state.clone(),
            cons_out,
            cons_lb,
            out_error_flag.clone(),
        )
        .unwrap();

        save_prefs(
            prefs.client_id,
            &prefs.nickname,
            &prefs.room,
            &prefs.password,
            prefs.ptt_enabled,
            prefs.ptt_vk,
            prefs.boost_enabled,
            prefs.sounds_enabled,
            prefs.ns_level,
            &mic_name,
            &out_name,
        );

        // === ПОТОК ПОИСКА УЧАСТНИКОВ ЧЕРЕЗ GET, KEEP-ALIVE POST И UDP HOLE PUNCHING ===
        let state_beacon = state.clone();
        let socket_punch = socket_tx.try_clone().unwrap();
        thread::spawn(move || {
            let mut last_sync = Instant::now() - Duration::from_secs(10);
            let mut last_announce = Instant::now();
            let mut was_in_room = false;

            loop {
                let in_room = state_beacon.room.in_room.load(Ordering::Relaxed);
                if in_room && !was_in_room {
                    last_sync = Instant::now() - Duration::from_secs(10);
                    last_announce = Instant::now();
                }
                was_in_room = in_room;

                if in_room && last_sync.elapsed() >= Duration::from_secs(2) {
                    let room_hash = state_beacon.room.room_hash.lock().unwrap().clone();
                    let key = *state_beacon.room.room_key.lock().unwrap();
                    let my_id = state_beacon.room.my_id;

                    if last_announce.elapsed() >= Duration::from_secs(20) {
                        let pub_addr = *state_beacon.public_addr.lock().unwrap();
                        let my_blob = encrypt_addr_blob(pub_addr, &key);
                        let _ = beacon_sync_mesh(&room_hash, my_id, &my_blob);
                        last_announce = Instant::now();
                    }

                    if let Ok(mesh_list) = beacon_fetch_mesh(&room_hash) {
                        let my_name = state_beacon.room.my_name.lock().unwrap().clone();
                        let name_bytes = my_name.as_bytes();
                        let n_len = name_bytes.len().min(20);
                        let mut ping_pkt = Vec::with_capacity(10 + n_len);
                        ping_pkt.push(PKT_PING);
                        ping_pkt.extend_from_slice(&my_id.to_be_bytes());
                        ping_pkt.push(n_len as u8);
                        ping_pkt.extend_from_slice(&name_bytes[..n_len]);

                        let mut targets_to_punch: Vec<SocketAddr> = Vec::new();
                        {
                            let mut peers = state_beacon.room.peers.lock().unwrap();
                            for (pid, blob) in mesh_list {
                                if pid == my_id {
                                    continue;
                                }
                                if let Ok(peer_addr) = decrypt_addr_blob(&blob, &key) {
                                    if !targets_to_punch.contains(&peer_addr) {
                                        targets_to_punch.push(peer_addr);
                                    }

                                    if let Some(existing) = peers.get_mut(&pid) {
                                        if !existing.connected {
                                            existing.addr = peer_addr;
                                            existing.last_seen = Instant::now();
                                        }
                                    } else if peers.len() + 1 < MAX_ROOM_USERS {
                                        if let Ok(dec) = Decoder::new(SAMPLE_RATE, Channels::Mono) {
                                            peers.insert(
                                                pid,
                                                PeerNode {
                                                    id: pid,
                                                    name: format!("Player_{:04}", pid % 10000),
                                                    addr: peer_addr,
                                                    volume: 1.0,
                                                    last_seen: Instant::now(),
                                                    last_spoke: Instant::now() - Duration::from_secs(5),
                                                    connected: false,
                                                    last_seq: None,
                                                    jitter_primed: false,
                                                    decoder: dec,
                                                    audio_queue: Vec::with_capacity(FRAME_SIZE * 6),
                                                },
                                            );
                                        }
                                    }
                                }
                            }
                        }

                        for _ in 0..4 {
                            for addr in &targets_to_punch {
                                let _ = socket_punch.send_to(&ping_pkt, addr);
                            }
                            thread::sleep(Duration::from_millis(120));
                        }
                    }

                    last_sync = Instant::now();
                }

                thread::sleep(Duration::from_millis(200));
            }
        });

        // === ПОТОК ОТПРАВКИ, ШУМОДАВА, ГЕЙТА ТИШИНЫ, БУСТА И ЖИВОГО LOOPBACK ===
        let state_tx = state.clone();
        let cons_in_tx_arc = cons_in_shared.clone();
        let prod_lb_tx_arc = prod_lb_shared.clone();
        thread::spawn(move || {
            let mut denoise = DenoiseState::new();
            let mut encoder = Encoder::new(SAMPLE_RATE, Channels::Mono, Application::Voip).unwrap();
            encoder.set_bitrate(opus::Bitrate::Bits(48_000)).unwrap();

            let mut raw_frame = [0.0f32; FRAME_SIZE];
            let mut clean_frame = [0.0f32; FRAME_SIZE];
            let mut opus_packet = [0u8; 256];

            let mut vad_hold_frames: u32 = 0;
            let mut ptt_hold_frames: u32 = 0;
            let mut current_gain: f32 = 1.0;
            let mut gate_env: f32 = 0.0;
            let mut seq_num: u64 = 0;
            let mut last_heartbeat = Instant::now();

            loop {
                let in_room = state_tx.room.in_room.load(Ordering::Relaxed);

                if in_room && last_heartbeat.elapsed() >= Duration::from_millis(350) {
                    let my_id = state_tx.room.my_id;
                    let my_name = state_tx.room.my_name.lock().unwrap().clone();
                    let name_bytes = my_name.as_bytes();
                    let n_len = name_bytes.len().min(20);

                    let mut ping_pkt = Vec::with_capacity(10 + n_len);
                    ping_pkt.push(PKT_PING);
                    ping_pkt.extend_from_slice(&my_id.to_be_bytes());
                    ping_pkt.push(n_len as u8);
                    ping_pkt.extend_from_slice(&name_bytes[..n_len]);

                    let (peer_addrs, connected_count, any_dropped): (Vec<SocketAddr>, usize, bool) = {
                        let mut peers = state_tx.room.peers.lock().unwrap();
                        let mut dropped = false;
                        peers.retain(|_, p| {
                            let keep = p.last_seen.elapsed() < Duration::from_secs(8);
                            if !keep && p.connected {
                                dropped = true;
                            }
                            keep
                        });
                        let addrs = peers.values().map(|p| p.addr).collect();
                        let conn = peers.values().filter(|p| p.connected).count();
                        (addrs, conn, dropped)
                    };
                    if any_dropped {
                        state_tx.play_cue(UiCueKind::Leave, false);
                    }

                    for addr in &peer_addrs {
                        let _ = socket_tx.send_to(&ping_pkt, addr);
                    }

                    *state_tx.status_text.lock().unwrap() =
                        format!("Online ({}/{})", connected_count + 1, MAX_ROOM_USERS);

                    last_heartbeat = Instant::now();
                }

                let has_in_frame = {
                    let mut cons_in_tx = cons_in_tx_arc.lock().unwrap();
                    if cons_in_tx.occupied_len() >= FRAME_SIZE {
                        for sample in raw_frame.iter_mut() {
                            let s = cons_in_tx.try_pop().unwrap_or(0.0).clamp(-0.98, 0.98);
                            *sample = s * 32767.0;
                        }
                        true
                    } else {
                        false
                    }
                };

                if has_in_frame {

                    let muted = state_tx.muted.load(Ordering::Relaxed)
                        || state_tx.deafened.load(Ordering::Relaxed);

                    if muted {
                        state_tx.my_speaking.store(false, Ordering::Relaxed);
                        state_tx.ptt_active.store(false, Ordering::Relaxed);
                        state_tx.set_my_level(0.0);
                        gate_env = 0.0;
                        continue;
                    }

                    // 1. Шумоподавление nnnoiseless + плавная настройка порога (ns_level 1..10) без обрезания речи
                    let ns = state_tx.ns_level.load(Ordering::Relaxed).clamp(1, 10) as f32;
                    let norm_ns = (ns - 1.0) / 9.0; // 0.0 .. 1.0

                    let vad_prob = denoise.process_frame(&mut clean_frame, &raw_frame);
                    let mut sum_sq = 0.0f32;
                    for s in clean_frame.iter_mut() {
                        *s /= 32767.0;
                        sum_sq += *s * *s;
                    }
                    let rms = (sum_sq / FRAME_SIZE as f32).sqrt();

                    // Умеренный диапазон порогов, чтобы голос не «рассыпался» на слоги при любом значении ползунка
                    let primary_vad_thresh = 0.14 + norm_ns * 0.22; // 0.14 .. 0.36
                    let primary_rms_thresh = 0.0018 + norm_ns * 0.0042; // 0.0018 .. 0.0060
                    let secondary_vad_thresh = 0.10 + norm_ns * 0.16; // 0.10 .. 0.26
                    let secondary_rms_thresh = 0.0032 + norm_ns * 0.0048; // 0.0032 .. 0.0080
                    let hold_primary: u32 = ((32.0 - norm_ns * 8.0).round() as u32).max(20);
                    let hold_secondary: u32 = ((20.0 - norm_ns * 5.0).round() as u32).max(14);

                    if vad_prob > primary_vad_thresh && rms > primary_rms_thresh {
                        vad_hold_frames = hold_primary;
                    } else if vad_prob > secondary_vad_thresh && rms > secondary_rms_thresh {
                        vad_hold_frames = vad_hold_frames.max(hold_secondary);
                    } else if vad_hold_frames > 0 {
                        vad_hold_frames -= 1;
                    }

                    let ptt_mode = state_tx.ptt_enabled.load(Ordering::Relaxed);
                    let speaking = if ptt_mode {
                        let vk = state_tx.ptt_vk.load(Ordering::Relaxed);
                        let key_down = is_vk_pressed(vk);
                        state_tx.ptt_active.store(key_down, Ordering::Relaxed);

                        if key_down {
                            ptt_hold_frames = 22;
                        } else if ptt_hold_frames > 0 {
                            ptt_hold_frames -= 1;
                        }
                        ptt_hold_frames > 0 && vad_hold_frames > 0
                    } else {
                        state_tx.ptt_active.store(false, Ordering::Relaxed);
                        vad_hold_frames > 0
                    };

                    // 2. Плавный гейт тишины с мягким спадом (~100-140 мс), чтобы не рвать окончания слов
                    let target_env = if speaking { 1.0 } else { 0.0 };
                    let close_step = 0.07 + norm_ns * 0.05;
                    if target_env > gate_env {
                        gate_env = (gate_env + 0.55).min(1.0);
                    } else {
                        gate_env = (gate_env - close_step).max(0.0);
                    }

                    // 3. Опция БУСТ (автоусиление + контроль потолка при высоком уровне шумодава)
                    let boost_on = state_tx.boost_enabled.load(Ordering::Relaxed);
                    let capped_max_gain = MAX_GAIN - norm_ns * 2.5; // 6.5 .. 4.0
                    if boost_on {
                        if speaking && vad_prob > (primary_vad_thresh * 0.85) && rms > primary_rms_thresh {
                            let desired_gain = (TARGET_RMS / rms).clamp(MIN_GAIN, capped_max_gain);
                            if desired_gain < current_gain {
                                current_gain = current_gain * 0.85 + desired_gain * 0.15;
                            } else {
                                current_gain = current_gain * 0.96 + desired_gain * 0.04;
                            }
                        }
                    } else {
                        current_gain = current_gain * 0.85 + 1.0 * 0.15;
                    }

                    if gate_env <= 0.001 {
                        clean_frame.fill(0.0);
                    } else {
                        let step_env = gate_env;
                        for s in clean_frame.iter_mut() {
                            let amplified = *s * current_gain * step_env;
                            *s = if boost_on {
                                amplified.tanh()
                            } else {
                                amplified.clamp(-0.98, 0.98)
                            };
                        }
                    }

                    let active_audio = gate_env > 0.001;
                    state_tx.my_speaking.store(active_audio, Ordering::Relaxed);
                    let display_lvl = if active_audio {
                        (rms * current_gain * 4.5).clamp(0.05, 1.0)
                    } else {
                        0.0
                    };
                    state_tx.set_my_level(display_lvl);

                    // 4. Живой loopback (локальный тест, не уходит в сеть)
                    let loopback_on = state_tx.loopback_enabled.load(Ordering::Relaxed);
                    if loopback_on && active_audio {
                        let mut prod_lb_tx = prod_lb_tx_arc.lock().unwrap();
                        if prod_lb_tx.vacant_len() >= FRAME_SIZE {
                            for &s in &clean_frame {
                                let _ = prod_lb_tx.try_push(s);
                            }
                        }
                    }

                    // 5. Отправка в комнату по UDP (только если не включен режим локального теста)
                    if in_room && !loopback_on && active_audio {
                        if let Ok(packet_len) = encoder.encode_float(&clean_frame, &mut opus_packet)
                        {
                            seq_num += 1;
                            let mut nonce_bytes = [0u8; 12];
                            nonce_bytes[4..12].copy_from_slice(&seq_num.to_be_bytes());
                            let nonce = Nonce::from_slice(&nonce_bytes);

                            let key = *state_tx.room.room_key.lock().unwrap();
                            let cipher = ChaCha20Poly1305::new(&key.into());

                            if let Ok(ciphertext) =
                                cipher.encrypt(nonce, &opus_packet[..packet_len])
                            {
                                let my_id = state_tx.room.my_id;
                                let mut udp_pkt = Vec::with_capacity(17 + ciphertext.len());
                                udp_pkt.push(PKT_VOICE);
                                udp_pkt.extend_from_slice(&my_id.to_be_bytes());
                                udp_pkt.extend_from_slice(&seq_num.to_be_bytes());
                                udp_pkt.extend_from_slice(&ciphertext);

                                let targets: Vec<SocketAddr> = {
                                    let peers = state_tx.room.peers.lock().unwrap();
                                    peers.values().map(|p| p.addr).collect()
                                };

                                for addr in targets {
                                    let _ = socket_tx.send_to(&udp_pkt, addr);
                                }
                            }
                        }
                    }
                } else {
                    thread::sleep(Duration::from_millis(1));
                }
            }
        });

        // === ПОТОК ПРИЕМА И МИКШЕРА ===
        let state_rx = state.clone();
        let prod_out_rx_arc = prod_out_shared.clone();
        thread::spawn(move || {
            let mut decoded_frame = [0.0f32; FRAME_SIZE];
            let mut udp_buf = [0u8; 1500];

            loop {
                let mut got_packet = false;

                loop {
                    match socket_rx.recv_from(&mut udp_buf) {
                        Ok((len, src)) if len >= 1 => {
                            got_packet = true;
                            if !state_rx.room.in_room.load(Ordering::Relaxed) {
                                continue;
                            }

                            let pkt_type = udp_buf[0];
                            let my_id = state_rx.room.my_id;

                            if pkt_type == PKT_PING && len >= 10 {
                                let sender_id =
                                    u64::from_be_bytes(udp_buf[1..9].try_into().unwrap());
                                if sender_id == my_id {
                                    continue;
                                }
                                let n_len = (udp_buf[9] as usize).min(len - 10);
                                let name =
                                    String::from_utf8_lossy(&udp_buf[10..10 + n_len]).to_string();

                                let mut peers = state_rx.room.peers.lock().unwrap();
                                if let Some(p) = peers.get_mut(&sender_id) {
                                    let was_conn = p.connected;
                                    p.addr = src;
                                    p.last_seen = Instant::now();
                                    p.connected = true;
                                    if !was_conn {
                                        state_rx.play_cue(UiCueKind::Join, false);
                                    }
                                    if !name.is_empty() {
                                        p.name = name;
                                    }
                                } else if peers.len() + 1 < MAX_ROOM_USERS {
                                    if let Ok(dec) = Decoder::new(SAMPLE_RATE, Channels::Mono) {
                                        peers.insert(
                                            sender_id,
                                            PeerNode {
                                                id: sender_id,
                                                name: if name.is_empty() {
                                                    format!("Player_{:04}", sender_id % 10000)
                                                } else {
                                                    name
                                                },
                                                addr: src,
                                                                                                volume: 1.0,
                                                last_seen: Instant::now(),
                                                last_spoke: Instant::now() - Duration::from_secs(5),
                                                connected: true,
                                                last_seq: None,
                                                jitter_primed: false,
                                                decoder: dec,
                                                audio_queue: Vec::with_capacity(FRAME_SIZE * 6),
                                            },
                                        );
                                    }
                                }
                            } else if pkt_type == PKT_VOICE && len > 17 {
                                let sender_id =
                                    u64::from_be_bytes(udp_buf[1..9].try_into().unwrap());
                                if sender_id == my_id {
                                    continue;
                                }
                                let pkt_seq =
                                    u64::from_be_bytes(udp_buf[9..17].try_into().unwrap());

                                let mut nonce_bytes = [0u8; 12];
                                nonce_bytes[4..12].copy_from_slice(&udp_buf[9..17]);
                                let nonce = Nonce::from_slice(&nonce_bytes);

                                let key = *state_rx.room.room_key.lock().unwrap();
                                let cipher = ChaCha20Poly1305::new(&key.into());

                                if let Ok(opus_data) = cipher.decrypt(nonce, &udp_buf[17..len]) {
                                    let mut peers = state_rx.room.peers.lock().unwrap();
                                    if !peers.contains_key(&sender_id)
                                        && peers.len() + 1 < MAX_ROOM_USERS
                                    {
                                        if let Ok(dec) = Decoder::new(SAMPLE_RATE, Channels::Mono) {
                                            peers.insert(
                                                sender_id,
                                                PeerNode {
                                                    id: sender_id,
                                                    name: format!("Player_{:04}", sender_id % 10000),
                                                    addr: src,
                                                                                                        volume: 1.0,
                                                    last_seen: Instant::now(),
                                                    last_spoke: Instant::now(),
                                                    connected: true,
                                                    last_seq: None,
                                                    jitter_primed: false,
                                                    decoder: dec,
                                                    audio_queue: Vec::with_capacity(FRAME_SIZE * 8),
                                                },
                                            );
                                        }
                                    }

                                    if let Some(peer) = peers.get_mut(&sender_id) {
                                        peer.addr = src;
                                        peer.last_seen = Instant::now();
                                        peer.connected = true;

                                        if let Some(prev_seq) = peer.last_seq {
                                            if pkt_seq <= prev_seq {
                                                continue;
                                            }
                                            let lost = pkt_seq - prev_seq - 1;
                                            if lost > 0 && lost <= 6 {
                                                let plc_frames = lost.min(2);
                                                for _ in 0..plc_frames {
                                                    if let Ok(plc_len) = peer.decoder.decode_float(
                                                        &[],
                                                        &mut decoded_frame,
                                                        true,
                                                    ) {
                                                        peer.audio_queue.extend_from_slice(
                                                            &decoded_frame[..plc_len],
                                                        );
                                                    }
                                                }
                                            } else if lost > 6 {
                                                peer.jitter_primed = false;
                                            }
                                        }
                                        peer.last_seq = Some(pkt_seq);

                                        if let Ok(decoded_len) = peer.decoder.decode_float(
                                            &opus_data,
                                            &mut decoded_frame,
                                            false,
                                        ) {
                                            peer.last_spoke = Instant::now();
                                            if peer.audio_queue.len() > FRAME_SIZE * 8 {
                                                let excess =
                                                    peer.audio_queue.len() - FRAME_SIZE * 4;
                                                peer.audio_queue.drain(0..excess);
                                            }
                                            peer.audio_queue
                                                .extend_from_slice(&decoded_frame[..decoded_len]);
                                        }
                                    }
                                }
                            }
                        }
                        _ => break,
                    }
                }

                loop {
                    let mut mixed = [0.0f32; FRAME_SIZE];
                    let mut any_ready = false;

                    {
                        let mut peers = state_rx.room.peers.lock().unwrap();
                        for peer in peers.values_mut() {
                            if !peer.jitter_primed {
                                if peer.audio_queue.len() >= FRAME_SIZE * 2 {
                                    peer.jitter_primed = true;
                                } else {
                                    continue;
                                }
                            }
                            if peer.audio_queue.len() >= FRAME_SIZE {
                                any_ready = true;
                                let vol = peer.volume;
                                for (i, s) in peer.audio_queue.drain(0..FRAME_SIZE).enumerate() {
                                    mixed[i] += s * vol;
                                }
                            }
                        }
                    }

                    if any_ready {
                        let mut prod_out_rx = prod_out_rx_arc.lock().unwrap();
                        for &s in &mixed {
                            let _ = prod_out_rx.try_push(s.tanh());
                        }
                    } else {
                        break;
                    }
                }

                if !got_packet {
                    thread::sleep(Duration::from_millis(1));
                }
            }
        });

        let available_update = Arc::new(Mutex::new(None));
        let update_slot = available_update.clone();
        thread::spawn(move || {
            if let Some(info) = check_github_latest_release() {
                *update_slot.lock().unwrap() = Some(info);
            }
        });

        Self {
            state,
            client_id: prefs.client_id,
            room_input: prefs.room,
            pass_input: prefs.password,
            nickname_input: prefs.nickname,
            joining_in_progress: Arc::new(AtomicBool::new(false)),
            binding_ptt_key: false,
            mic_name,
            out_name,
            available_mics,
            available_outs,
            last_device_scan: Instant::now(),
            cons_in_shared,
            prod_out_shared,
            prod_lb_shared,
            available_update,
            desk_texture,
            welcome_game: MiniGameAnim::default(),
            audio_epoch,
            in_error_flag,
            in_heartbeat_ms,
            out_error_flag,
            last_audio_recovery: Instant::now(),
            input_stream: Some(input_stream),
            output_stream: Some(output_stream),
        }
    }

    fn switch_input_device(&mut self, desired_name: &str) {
        let host = cpal::default_host();
        if let Ok(dev) = find_input_device(&host, desired_name) {
            let old_stream = self.input_stream.take();
            drop(old_stream);

            self.in_error_flag.store(false, Ordering::Relaxed);
            self.in_heartbeat_ms.store(
                self.audio_epoch.elapsed().as_millis() as u32,
                Ordering::Relaxed,
            );

            let (new_prod, new_cons) = HeapRb::<f32>::new(FRAME_SIZE * 24).split();
            if let Ok((new_stream, actual_name)) = build_input_stream_for_device(
                &dev,
                new_prod,
                self.in_error_flag.clone(),
                self.in_heartbeat_ms.clone(),
                self.audio_epoch,
            ) {
                *self.cons_in_shared.lock().unwrap() = new_cons;
                self.input_stream = Some(new_stream);
                self.mic_name = actual_name;
                self.persist_current_prefs();
            } else if let Ok(fallback_dev) = find_input_device(&host, "") {
                let (fb_prod, fb_cons) = HeapRb::<f32>::new(FRAME_SIZE * 24).split();
                if let Ok((fb_stream, fb_name)) = build_input_stream_for_device(
                    &fallback_dev,
                    fb_prod,
                    self.in_error_flag.clone(),
                    self.in_heartbeat_ms.clone(),
                    self.audio_epoch,
                ) {
                    *self.cons_in_shared.lock().unwrap() = fb_cons;
                    self.input_stream = Some(fb_stream);
                    self.mic_name = fb_name;
                    self.persist_current_prefs();
                }
            }
        }
    }

    fn switch_output_device(&mut self, desired_name: &str) {
        let host = cpal::default_host();
        if let Ok(dev) = find_output_device(&host, desired_name) {
            let old_stream = self.output_stream.take();
            drop(old_stream);

            self.out_error_flag.store(false, Ordering::Relaxed);

            let (new_prod_out, new_cons_out) = HeapRb::<f32>::new(FRAME_SIZE * 28).split();
            let (new_prod_lb, new_cons_lb) = HeapRb::<f32>::new(FRAME_SIZE * 16).split();
            if let Ok((new_stream, actual_name)) = build_output_stream_for_device(
                &dev,
                self.state.clone(),
                new_cons_out,
                new_cons_lb,
                self.out_error_flag.clone(),
            ) {
                *self.prod_out_shared.lock().unwrap() = new_prod_out;
                *self.prod_lb_shared.lock().unwrap() = new_prod_lb;
                self.output_stream = Some(new_stream);
                self.out_name = actual_name;
                self.persist_current_prefs();
            } else if let Ok(fallback_dev) = find_output_device(&host, "") {
                let (fb_prod_out, fb_cons_out) = HeapRb::<f32>::new(FRAME_SIZE * 28).split();
                let (fb_prod_lb, fb_cons_lb) = HeapRb::<f32>::new(FRAME_SIZE * 16).split();
                if let Ok((fb_stream, fb_name)) = build_output_stream_for_device(
                    &fallback_dev,
                    self.state.clone(),
                    fb_cons_out,
                    fb_cons_lb,
                    self.out_error_flag.clone(),
                ) {
                    *self.prod_out_shared.lock().unwrap() = fb_prod_out;
                    *self.prod_lb_shared.lock().unwrap() = fb_prod_lb;
                    self.output_stream = Some(fb_stream);
                    self.out_name = fb_name;
                    self.persist_current_prefs();
                }
            }
        }
    }

    fn persist_current_prefs(&self) {
        save_prefs(
            self.client_id,
            self.nickname_input.trim(),
            self.room_input.trim(),
            self.pass_input.trim(),
            self.state.ptt_enabled.load(Ordering::Relaxed),
            self.state.ptt_vk.load(Ordering::Relaxed),
            self.state.boost_enabled.load(Ordering::Relaxed),
            self.state.sounds_enabled.load(Ordering::Relaxed),
            self.state.ns_level.load(Ordering::Relaxed),
            &self.mic_name,
            &self.out_name,
        );
    }

        fn enter_room(&mut self) {
        if self.joining_in_progress.load(Ordering::Relaxed) {
            return;
        }
        let room_name = self.room_input.trim().to_string();
        let password = self.pass_input.trim().to_string();
        if room_name.is_empty() {
            *self.state.status_text.lock().unwrap() = "Введи название комнаты".to_string();
            return;
        }

        self.persist_current_prefs();

        self.joining_in_progress.store(true, Ordering::Relaxed);
        *self.state.status_text.lock().unwrap() = "Подключение к комнате...".to_string();

        let state = self.state.clone();
        let joining_flag = self.joining_in_progress.clone();

        thread::spawn(move || {
            let (room_hash, key) = derive_room_secrets(&room_name, &password);
            let my_id = state.room.my_id;
            let pub_addr = *state.public_addr.lock().unwrap();
            let my_blob = encrypt_addr_blob(pub_addr, &key);

            match beacon_sync_mesh(&room_hash, my_id, &my_blob) {
                Ok(mesh_list) => {
                    *state.room.room_hash.lock().unwrap() = room_hash;
                    *state.room.room_key.lock().unwrap() = key;

                    let mut peers = state.room.peers.lock().unwrap();
                    peers.clear();

                    for (pid, blob) in mesh_list {
                        if pid == my_id {
                            continue;
                        }
                        if let Ok(peer_addr) = decrypt_addr_blob(&blob, &key) {
                            if peers.len() + 1 < MAX_ROOM_USERS {
                                if let Ok(dec) = Decoder::new(SAMPLE_RATE, Channels::Mono) {
                                    peers.insert(
                                        pid,
                                        PeerNode {
                                            id: pid,
                                            name: format!("Player_{:04}", pid % 10000),
                                            addr: peer_addr,
                                            volume: 1.0,
                                            last_seen: Instant::now(),
                                            last_spoke: Instant::now() - Duration::from_secs(5),
                                            connected: false,
                                            last_seq: None,
                                            jitter_primed: false,
                                            decoder: dec,
                                            audio_queue: Vec::with_capacity(FRAME_SIZE * 6),
                                        },
                                    );
                                }
                            }
                        }
                    }

                    state.room.in_room.store(true, Ordering::Relaxed);
                    *state.status_text.lock().unwrap() = "Online (1/20)".to_string();
                    state.play_cue(UiCueKind::Join, false);
                }
                Err(_) => {
                    *state.status_text.lock().unwrap() =
                        "Нет связи с маячком (проверь BEACON_URL)".to_string();
                }
            }

            joining_flag.store(false, Ordering::Relaxed);
        });
    }

    fn leave_room(&mut self) {
        let room_hash = self.state.room.room_hash.lock().unwrap().clone();
        let my_id = self.state.room.my_id;

        let was_in_room = self.state.room.in_room.swap(false, Ordering::Relaxed);
        self.state.room.peers.lock().unwrap().clear();
        *self.state.status_text.lock().unwrap() = "Offline".to_string();
        if was_in_room {
            self.state.play_cue(UiCueKind::Leave, false);
        }

        if !room_hash.is_empty() {
            thread::spawn(move || {
                beacon_leave_mesh(&room_hash, my_id);
            });
        }
    }
}

fn retro_window_box(
    ui: &mut egui::Ui,
    title: &str,
    accent_border: bool,
    add_contents: impl FnOnce(&mut egui::Ui),
) {
    let border_color = if accent_border {
        RETRO_PINK
    } else {
        RETRO_BORDER
    };

    egui::Frame::none()
        .fill(PANEL_BLACK)
        .stroke(egui::Stroke::new(1.0_f32, border_color))
        .rounding(egui::Rounding::ZERO)
        .inner_margin(egui::Margin::same(0.0_f32))
        .show(ui, |ui| {
            ui.set_width(ui.available_width());

            let bar_height = 22.0_f32;
            let (bar_rect, _) = ui.allocate_exact_size(
                egui::vec2(ui.available_width(), bar_height),
                egui::Sense::hover(),
            );
            ui.painter().line_segment(
                [bar_rect.left_bottom(), bar_rect.right_bottom()],
                egui::Stroke::new(1.0_f32, border_color),
            );

            ui.painter().text(
                bar_rect.left_center() + egui::vec2(8.0, 0.0),
                egui::Align2::LEFT_CENTER,
                title,
                egui::FontId::proportional(10.5),
                egui::Color32::WHITE,
            );

            let box_rect = egui::Rect::from_min_size(
                egui::pos2(bar_rect.right() - 18.0, bar_rect.top() + 3.0),
                egui::vec2(14.0, 14.0),
            );
            ui.painter()
                .rect_stroke(box_rect, 0.0, egui::Stroke::new(1.0_f32, border_color));
            ui.painter().text(
                box_rect.center(),
                egui::Align2::CENTER_CENTER,
                "x",
                egui::FontId::proportional(10.0),
                border_color,
            );

            egui::Frame::none()
                .inner_margin(egui::Margin::same(10.0_f32))
                .show(ui, add_contents);
        });
}

/// Компактный ретро-ползунок громкости (0%..200%) в стиле интерфейса GGVoice
fn retro_volume_bar(ui: &mut egui::Ui, volume: &mut f32) -> bool {
    let desired_size = egui::vec2(84.0, 12.0);
    let (rect, response) =
        ui.allocate_exact_size(desired_size, egui::Sense::click_and_drag());
    let mut changed = false;

    if response.double_clicked() {
        *volume = 1.0;
        changed = true;
    } else if response.dragged() || response.clicked() {
        if let Some(pos) = response.interact_pointer_pos() {
            let t = ((pos.x - rect.left()) / rect.width()).clamp(0.0, 1.0);
            *volume = t * 2.0;
            changed = true;
        }
    }

    let painter = ui.painter();
    let border_col = if response.hovered() || response.dragged() {
        CYBER_MINT
    } else {
        RETRO_PINK
    };

    painter.rect_filled(rect, 0.0, VOID_BLACK);
    painter.rect_stroke(rect, 0.0, egui::Stroke::new(1.0_f32, border_col));

    let norm = (*volume / 2.0).clamp(0.0, 1.0);
    let inner_w = rect.width() - 4.0;
    if norm > 0.01 {
        let fill_rect = egui::Rect::from_min_size(
            rect.min + egui::vec2(2.0, 2.0),
            egui::vec2((inner_w * norm).max(2.0), rect.height() - 4.0),
        );
        painter.rect_filled(fill_rect, 0.0, RETRO_PINK_DIM);
    }

    let knob_x = rect.left() + 2.0 + inner_w * norm;
    painter.line_segment(
        [
            egui::pos2(knob_x, rect.top() + 1.0),
            egui::pos2(knob_x, rect.bottom() - 1.0),
        ],
        egui::Stroke::new(2.0_f32, egui::Color32::WHITE),
    );

    changed
}

/// Минималистичная плоская ретро-кнопка выбора устройства без стандартного комбобокса
fn retro_device_selector(
    ui: &mut egui::Ui,
    id_salt: &str,
    prefix: &str,
    current_name: &str,
    devices: &[String],
    width: f32,
) -> Option<String> {
    let mut picked: Option<String> = None;
    let short_name = compact_device_label(current_name, 17);
    let display_text = format!("{} {}", prefix, short_name);

    let (rect, response) =
        ui.allocate_exact_size(egui::vec2(width, 20.0), egui::Sense::click());

    let popup_id = ui.make_persistent_id(id_salt);
    if response.clicked() {
        ui.memory_mut(|mem| mem.toggle_popup(popup_id));
    }

    let is_open = ui.memory(|mem| mem.is_popup_open(popup_id));
    let border_col = if is_open {
        RETRO_PINK
    } else if response.hovered() {
        CYBER_MINT
    } else {
        RETRO_BORDER
    };

    let painter = ui.painter();
    painter.rect_filled(rect, 0.0, PANEL_BLACK);
    painter.rect_stroke(rect, 0.0, egui::Stroke::new(1.0_f32, border_col));

    painter.text(
        rect.left_center() + egui::vec2(6.0, 0.0),
        egui::Align2::LEFT_CENTER,
        display_text,
        egui::FontId::proportional(9.0),
        egui::Color32::WHITE,
    );

    painter.text(
        rect.right_center() - egui::vec2(6.0, 0.0),
        egui::Align2::RIGHT_CENTER,
        if is_open { "▲" } else { "▼" },
        egui::FontId::proportional(7.5),
        if is_open { RETRO_PINK } else { RETRO_GRAY },
    );

    egui::popup_above_or_below_widget(
        ui,
        popup_id,
        &response,
        egui::AboveOrBelow::Above,
        egui::PopupCloseBehavior::CloseOnClick,
        |ui| {
            egui::Frame::none()
                .fill(PANEL_BLACK)
                .stroke(egui::Stroke::new(1.0_f32, RETRO_PINK))
                .rounding(egui::Rounding::ZERO)
                .inner_margin(egui::Margin::same(4.0))
                .show(ui, |ui| {
                    ui.set_min_width(width.max(210.0));
                    for dev_name in devices {
                        let is_sel = dev_name == current_name;
                        let item_label = if is_sel {
                            format!("▸ {}", compact_device_label(dev_name, 34))
                        } else {
                            format!("  {}", compact_device_label(dev_name, 34))
                        };
                        let btn = egui::Button::new(
                            egui::RichText::new(item_label)
                                .size(9.5)
                                .color(if is_sel {
                                    RETRO_PINK
                                } else {
                                    egui::Color32::WHITE
                                }),
                        )
                        .fill(if is_sel {
                            egui::Color32::from_rgb(28, 12, 22)
                        } else {
                            PANEL_BLACK
                        })
                        .stroke(egui::Stroke::NONE);

                        if ui.add_sized([ui.available_width(), 20.0], btn).clicked() {
                            picked = Some(dev_name.clone());
                        }
                    }
                });
        },
    );

    picked
}

impl eframe::App for GGVoiceApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        ctx.request_repaint_after(Duration::from_millis(16));

        if self.binding_ptt_key {
            if is_vk_pressed(0x1B) {
                self.binding_ptt_key = false;
            } else if let Some(vk) = poll_any_pressed_vk() {
                self.state.ptt_vk.store(vk, Ordering::Relaxed);
                self.binding_ptt_key = false;
                self.persist_current_prefs();
            }
        }

        if self.last_device_scan.elapsed() >= Duration::from_secs(3) {
            let host = cpal::default_host();
            self.available_mics = list_input_devices(&host);
            self.available_outs = list_output_devices(&host);
            self.last_device_scan = Instant::now();

            let now_ms = self.audio_epoch.elapsed().as_millis() as u32;
            let last_hb = self.in_heartbeat_ms.load(Ordering::Relaxed);
            let stalled_in = now_ms > 3000 && now_ms.saturating_sub(last_hb) > 1800;
            let mic_missing = !self.mic_name.is_empty() && !self.available_mics.contains(&self.mic_name);

            if (self.in_error_flag.load(Ordering::Relaxed) || stalled_in || mic_missing)
                && self.last_audio_recovery.elapsed() >= Duration::from_secs(3)
            {
                self.last_audio_recovery = Instant::now();
                let target = if mic_missing { "" } else { &self.mic_name.clone() };
                self.switch_input_device(target);
            }

            let out_missing = !self.out_name.is_empty() && !self.available_outs.contains(&self.out_name);
            if (self.out_error_flag.load(Ordering::Relaxed) || out_missing)
                && self.last_audio_recovery.elapsed() >= Duration::from_secs(3)
            {
                self.last_audio_recovery = Instant::now();
                let target = if out_missing { "" } else { &self.out_name.clone() };
                self.switch_output_device(target);
            }
        }

        // 1. НИЖНЯЯ СТАТИЧНАЯ ПАНЕЛЬ
        egui::TopBottomPanel::bottom("bottom_dock")
            .show_separator_line(false)
            .frame(
                egui::Frame::none()
                    .fill(VOID_BLACK)
                    .inner_margin(egui::Margin::symmetric(8.0_f32, 8.0_f32)),
            )
            .show(ctx, |ui| {
                let lvl = self.state.my_level();
                let ptt_on = self.state.ptt_enabled.load(Ordering::Relaxed);
                let ptt_down = self.state.ptt_active.load(Ordering::Relaxed);
                let lb_on = self.state.loopback_enabled.load(Ordering::Relaxed);
                let boost_on = self.state.boost_enabled.load(Ordering::Relaxed);

                let cur_ns = self.state.ns_level.load(Ordering::Relaxed).clamp(1, 10);
                ui.horizontal(|ui| {
                    ui.label(
                        egui::RichText::new(format!("ШУМОДАВ: {}/10", cur_ns))
                            .size(9.5)
                            .color(RETRO_GRAY),
                    );

                    ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                        let (ns_rect, ns_resp) = ui.allocate_exact_size(
                            egui::vec2(132.0, 11.0),
                            egui::Sense::click_and_drag(),
                        );
                        if ns_resp.double_clicked() {
                            self.state.ns_level.store(6, Ordering::Relaxed);
                            self.persist_current_prefs();
                        } else if ns_resp.clicked() || ns_resp.dragged() {
                            if let Some(pos) = ns_resp.interact_pointer_pos() {
                                let frac = ((pos.x - ns_rect.left()) / ns_rect.width()).clamp(0.0, 1.0);
                                let new_ns = ((frac * 9.0).round() as i32 + 1).clamp(1, 10);
                                if new_ns != cur_ns {
                                    self.state.ns_level.store(new_ns, Ordering::Relaxed);
                                    self.persist_current_prefs();
                                }
                            }
                        }

                        let p = ui.painter();
                        let bcol = if ns_resp.hovered() || ns_resp.dragged() {
                            CYBER_MINT
                        } else {
                            RETRO_BORDER
                        };
                        p.rect_filled(ns_rect, 0.0, PANEL_BLACK);
                        p.rect_stroke(ns_rect, 0.0, egui::Stroke::new(1.0_f32, bcol));
                        let ratio = (cur_ns as f32 - 1.0) / 9.0;
                        let inner_w = (ns_rect.width() - 4.0).max(2.0);
                        p.rect_filled(
                            egui::Rect::from_min_size(
                                ns_rect.min + egui::vec2(2.0, 2.0),
                                egui::vec2((inner_w * ratio).max(4.0), ns_rect.height() - 4.0),
                            ),
                            0.0,
                            RETRO_PINK,
                        );
                    });
                });

                ui.add_space(4.0);

                ui.horizontal(|ui| {
                    let sig_title = if lb_on {
                        if ptt_on && !ptt_down {
                            "ТЕСТ (РАЦИЯ): ЗАЖМИ КНОПКУ..."
                        } else {
                            "ТЕСТ МИКРОФОНА: СЛУШАЕШЬ СЕБЯ..."
                        }
                    } else if ptt_on {
                        if ptt_down {
                            "РАЦИЯ: В ЭФИРЕ..."
                        } else {
                            "РАЦИЯ: ЗАЖМИ КНОПКУ..."
                        }
                    } else {
                        "СИГНАЛ МИКРОФОНА..."
                    };
                    let sig_col = if lb_on || (ptt_on && ptt_down) {
                        CYBER_MINT
                    } else {
                        RETRO_GRAY
                    };

                    ui.label(egui::RichText::new(sig_title).size(9.5).color(sig_col));

                    ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                        let test_btn = egui::Button::new(
                            egui::RichText::new(if lb_on { "ТЕСТ: ВКЛ" } else { "ТЕСТ" })
                                .size(9.0)
                                .strong()
                                .color(if lb_on {
                                    VOID_BLACK
                                } else {
                                    CYBER_MINT
                                }),
                        )
                        .fill(if lb_on { CYBER_MINT } else { PANEL_BLACK });

                        if ui.add_sized([68.0, 18.0], test_btn).clicked() {
                            self.state
                                .loopback_enabled
                                .store(!lb_on, Ordering::Relaxed);
                        }

                        let sounds_on = self.state.sounds_enabled.load(Ordering::Relaxed);
                        let sound_btn = egui::Button::new(
                            egui::RichText::new(if sounds_on { "ЗВУК: ВКЛ" } else { "ЗВУК: ВЫКЛ" })
                                .size(9.0)
                                .strong()
                                .color(if sounds_on {
                                    VOID_BLACK
                                } else {
                                    RETRO_GRAY
                                }),
                        )
                        .fill(if sounds_on { RETRO_PINK } else { PANEL_BLACK });

                        if ui.add_sized([74.0, 18.0], sound_btn).clicked() {
                            let next_val = !sounds_on;
                            self.state
                                .sounds_enabled
                                .store(next_val, Ordering::Relaxed);
                            self.persist_current_prefs();
                            if next_val {
                                self.state.play_cue(UiCueKind::Join, true);
                            }
                        }

                        let boost_btn = egui::Button::new(
                            egui::RichText::new(if boost_on { "БУСТ: ВКЛ" } else { "БУСТ" })
                                .size(9.0)
                                .strong()
                                .color(if boost_on {
                                    VOID_BLACK
                                } else {
                                    RETRO_GRAY
                                }),
                        )
                        .fill(if boost_on { RETRO_PINK } else { PANEL_BLACK });

                        if ui.add_sized([62.0, 18.0], boost_btn).clicked() {
                            self.state
                                .boost_enabled
                                .store(!boost_on, Ordering::Relaxed);
                            self.persist_current_prefs();
                        }
                    });
                });

                ui.add_space(3.0);

                let (bar_rect, _) = ui.allocate_exact_size(
                    egui::vec2(ui.available_width(), 8.0),
                    egui::Sense::hover(),
                );
                let bar_color = if lb_on || (ptt_on && ptt_down) {
                    CYBER_MINT
                } else {
                    RETRO_PINK
                };
                ui.painter()
                    .rect_stroke(bar_rect, 0.0, egui::Stroke::new(1.0_f32, bar_color));
                if lvl > 0.01 {
                    let fill_w = (bar_rect.width() - 4.0) * lvl;
                    let fill_rect = egui::Rect::from_min_size(
                        bar_rect.min + egui::vec2(2.0, 2.0),
                        egui::vec2(fill_w.max(2.0), 4.0),
                    );
                    ui.painter().rect_filled(fill_rect, 0.0, bar_color);
                }

                ui.add_space(7.0);

                ui.horizontal(|ui| {
                    let mode_btn = egui::Button::new(
                        egui::RichText::new(if ptt_on {
                            "РЕЖИМ: ПО КНОПКЕ"
                        } else {
                            "РЕЖИМ: ПО ГОЛОСУ"
                        })
                        .size(10.0)
                        .strong()
                        .color(if ptt_on {
                            VOID_BLACK
                        } else {
                            egui::Color32::WHITE
                        }),
                    )
                    .fill(if ptt_on { RETRO_PINK } else { PANEL_BLACK });

                    let mode_w = if ptt_on {
                        (ui.available_width() - 8.0) * 0.55
                    } else {
                        ui.available_width()
                    };

                    if ui.add_sized([mode_w, 25.0], mode_btn).clicked() {
                        self.state.ptt_enabled.store(!ptt_on, Ordering::Relaxed);
                        self.binding_ptt_key = false;
                        self.persist_current_prefs();
                    }

                    if ptt_on {
                        let cur_vk = self.state.ptt_vk.load(Ordering::Relaxed);
                        let bind_text = if self.binding_ptt_key {
                            "НАЖМИ КЛАВИШУ..."
                        } else {
                            &format!("[ {} ]", vk_name(cur_vk))
                        };

                        let bind_btn = egui::Button::new(
                            egui::RichText::new(bind_text)
                                .size(10.0)
                                .strong()
                                .color(if self.binding_ptt_key {
                                    VOID_BLACK
                                } else {
                                    CYBER_MINT
                                }),
                        )
                        .fill(if self.binding_ptt_key {
                            CYBER_MINT
                        } else {
                            PANEL_BLACK
                        });

                        if ui.add_sized([ui.available_width(), 25.0], bind_btn).clicked() {
                            self.binding_ptt_key = !self.binding_ptt_key;
                        }
                    }
                });

                ui.add_space(7.0);

                ui.horizontal(|ui| {
                    let half_w = (ui.available_width() - 8.0) / 2.0;

                    let muted = self.state.muted.load(Ordering::Relaxed);
                    let mute_btn = egui::Button::new(
                        egui::RichText::new(if muted {
                            "МИКРОФОН ВЫКЛ"
                        } else {
                            "МИКРОФОН ВКЛ"
                        })
                        .size(11.0)
                        .strong()
                        .color(if muted {
                            VOID_BLACK
                        } else {
                            egui::Color32::WHITE
                        }),
                    )
                    .fill(if muted { RETRO_PINK } else { PANEL_BLACK });

                    if ui.add_sized([half_w, 30.0], mute_btn).clicked() {
                        self.state.muted.store(!muted, Ordering::Relaxed);
                    }

                    let deaf = self.state.deafened.load(Ordering::Relaxed);
                    let deaf_btn = egui::Button::new(
                        egui::RichText::new(if deaf {
                            "ЗВУК ВЫКЛ"
                        } else {
                            "ЗВУК ВКЛ"
                        })
                        .size(11.0)
                        .strong()
                        .color(if deaf {
                            VOID_BLACK
                        } else {
                            egui::Color32::WHITE
                        }),
                    )
                    .fill(if deaf { RETRO_PINK } else { PANEL_BLACK });

                    if ui.add_sized([half_w, 30.0], deaf_btn).clicked() {
                        self.state.deafened.store(!deaf, Ordering::Relaxed);
                    }
                });

                ui.add_space(7.0);

                // Компактные ретро-селекторы IN и OUT в одну строку без громоздких комбобоксов
                let mut picked_mic: Option<String> = None;
                let mut picked_out: Option<String> = None;
                ui.horizontal(|ui| {
                    let half_w = (ui.available_width() - 8.0) / 2.0;
                    picked_mic = retro_device_selector(
                        ui,
                        "gg_in_popup",
                        "IN:",
                        &self.mic_name,
                        &self.available_mics,
                        half_w,
                    );
                    picked_out = retro_device_selector(
                        ui,
                        "gg_out_popup",
                        "OUT:",
                        &self.out_name,
                        &self.available_outs,
                        half_w,
                    );
                });

                if let Some(new_mic) = picked_mic {
                    if new_mic != self.mic_name {
                        self.switch_input_device(&new_mic);
                    }
                }
                if let Some(new_out) = picked_out {
                    if new_out != self.out_name {
                        self.switch_output_device(&new_out);
                    }
                }
            });

        // 2. ОСНОВНАЯ ПАНЕЛЬ
        egui::CentralPanel::default().show(ctx, |ui| {
            let screen_rect = ctx.screen_rect();
            let painter = ui.painter();

            let step = 24.0_f32;
            let mut x = screen_rect.left();
            while x < screen_rect.right() {
                painter.line_segment(
                    [
                        egui::pos2(x, screen_rect.top()),
                        egui::pos2(x, screen_rect.bottom()),
                    ],
                    egui::Stroke::new(1.0_f32, GRID_LINE),
                );
                x += step;
            }
            let mut y = screen_rect.top();
            while y < screen_rect.bottom() {
                painter.line_segment(
                    [
                        egui::pos2(screen_rect.left(), y),
                        egui::pos2(screen_rect.right(), y),
                    ],
                    egui::Stroke::new(1.0_f32, GRID_LINE),
                );
                y += step;
            }

            let glitch_blocks = [
                (
                    screen_rect.right() - 32.0,
                    screen_rect.top() + 24.0,
                    6.0,
                    6.0,
                    RETRO_PINK,
                ),
                (
                    screen_rect.right() - 24.0,
                    screen_rect.top() + 30.0,
                    4.0,
                    4.0,
                    RETRO_PINK_DIM,
                ),
                (
                    screen_rect.right() - 28.0,
                    screen_rect.bottom() - 22.0,
                    5.0,
                    5.0,
                    RETRO_PINK,
                ),
                (
                    screen_rect.right() - 20.0,
                    screen_rect.bottom() - 16.0,
                    8.0,
                    4.0,
                    RETRO_PINK_DIM,
                ),
            ];
            for (gx, gy, gw, gh, col) in glitch_blocks {
                painter.rect_filled(
                    egui::Rect::from_min_size(egui::pos2(gx, gy), egui::vec2(gw, gh)),
                    0.0,
                    col,
                );
            }

            let update_prompt: Option<(String, String)> = self
                .available_update
                .lock()
                .unwrap()
                .as_ref()
                .map(|u| (u.tag_name.clone(), u.html_url.clone()));

            ui.horizontal(|ui| {
                ui.label(
                    egui::RichText::new(format!("▲ GGVoice_NODE // v{}", APP_VERSION))
                        .size(10.5)
                        .strong()
                        .color(RETRO_PINK),
                );

                if let Some((tag, url)) = update_prompt {
                    ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                        let label_txt = if tag.starts_with(['v', 'V']) {
                            format!("ОБНОВИТЬ {}", tag)
                        } else {
                            format!("ОБНОВИТЬ v{}", tag)
                        };
                        let upd_btn = egui::Button::new(
                            egui::RichText::new(label_txt)
                                .size(9.0)
                                .strong()
                                .color(VOID_BLACK),
                        )
                        .fill(CYBER_MINT);

                        if ui.add_sized([118.0, 18.0], upd_btn).clicked() {
                            open_url_in_browser(&url);
                        }
                    });
                }
            });

            ui.add_space(4.0);

            let title_pos = ui.cursor().min + egui::vec2(2.0, 0.0);
            ui.painter().text(
                title_pos + egui::vec2(2.0, 2.0),
                egui::Align2::LEFT_TOP,
                "GGVOICE",
                egui::FontId::proportional(32.0),
                RETRO_PINK,
            );
            ui.painter().text(
                title_pos,
                egui::Align2::LEFT_TOP,
                "GGVOICE",
                egui::FontId::proportional(32.0),
                egui::Color32::WHITE,
            );
            ui.add_space(36.0);

            let status = self.state.status_text.lock().unwrap().clone();
            let in_room = self.state.room.in_room.load(Ordering::Relaxed);
            let status_color = if in_room { CYBER_MINT } else { RETRO_PINK };

            ui.horizontal(|ui| {
                let dot = if in_room { "●" } else { "○" };
                ui.label(egui::RichText::new(dot).size(11.5).color(status_color));
                ui.label(
                    egui::RichText::new(status)
                        .size(11.0)
                        .strong()
                        .color(status_color),
                );

                ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                    if ui
                        .add_sized(
                            [120.0, 22.0],
                            egui::TextEdit::singleline(&mut self.nickname_input)
                                .hint_text("Твой ник"),
                        )
                        .changed()
                    {
                        let clean = self.nickname_input.trim();
                        if !clean.is_empty() {
                            *self.state.room.my_name.lock().unwrap() = clean.to_string();
                            self.persist_current_prefs();
                        }
                    }
                    ui.label(egui::RichText::new("НИК:").size(9.5).color(RETRO_GRAY));
                });
            });

            ui.add_space(8.0);

            if !in_room {
                retro_window_box(ui, "ВХОД В КОМНАТУ (ДО 20 ИГРОКОВ)", true, |ui| {
                    ui.horizontal(|ui| {
                        ui.label(egui::RichText::new("КОМНАТА:").size(10.0).color(RETRO_GRAY));
                        ui.add_sized(
                            [115.0, 24.0],
                            egui::TextEdit::singleline(&mut self.room_input)
                                .hint_text("Название"),
                        );

                        ui.label(egui::RichText::new("ПАРОЛЬ:").size(10.0).color(RETRO_GRAY));
                        ui.add_sized(
                            [ui.available_width(), 24.0],
                            egui::TextEdit::singleline(&mut self.pass_input)
                                .password(true)
                                .hint_text("Пароль"),
                        );
                    });

                    ui.add_space(8.0);

                    let busy = self.joining_in_progress.load(Ordering::Relaxed);
                    let btn_label = if busy {
                        "ПОДКЛЮЧЕНИЕ..."
                    } else {
                        "ВОЙТИ В КОМНАТУ"
                    };

                    if ui
                        .add_sized(
                            [ui.available_width(), 28.0],
                            egui::Button::new(
                                egui::RichText::new(btn_label)
                                    .size(11.0)
                                    .strong()
                                    .color(VOID_BLACK),
                            )
                            .fill(RETRO_PINK),
                        )
                        .clicked()
                    {
                        self.enter_room();
                    }
                });
            } else {
                retro_window_box(ui, "КОМНАТА АКТИВНА", true, |ui| {
                    ui.horizontal(|ui| {
                        ui.label(
                            egui::RichText::new(format!("КАНАЛ: {}", self.room_input.trim()))
                                .size(11.5)
                                .strong()
                                .color(egui::Color32::WHITE),
                        );

                        ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                            if ui
                                .add_sized(
                                    [95.0, 26.0],
                                    egui::Button::new(
                                        egui::RichText::new("ВЫЙТИ")
                                            .size(10.5)
                                            .strong()
                                            .color(RETRO_PINK),
                                    )
                                    .fill(PANEL_BLACK),
                                )
                                .clicked()
                            {
                                self.leave_room();
                            }
                        });
                    });
                });
            }

            ui.add_space(8.0);

            if !in_room {
                self.welcome_game.draw(ui, self.desk_texture.as_ref());
            } else {
                let connected_peers = self
                    .state
                    .room
                    .peers
                    .lock()
                    .unwrap()
                    .values()
                    .filter(|p| p.connected)
                    .count();
                let room_title = format!("УЧАСТНИКИ ({}/{})", connected_peers + 1, MAX_ROOM_USERS);

                retro_window_box(ui, &room_title, false, |ui| {
                    let list_h = (ui.available_height() - 4.0).max(80.0);
                    egui::ScrollArea::vertical()
                        .min_scrolled_height(list_h)
                        .max_height(list_h)
                        .show(ui, |ui| {
                            ui.set_width(ui.available_width());

                            let my_speak = self.state.my_speaking.load(Ordering::Relaxed);
                            let my_nick = self.state.room.my_name.lock().unwrap().clone();
                            ui.horizontal(|ui| {
                                let (sq_rect, _) = ui.allocate_exact_size(
                                    egui::vec2(12.0, 14.0),
                                    egui::Sense::hover(),
                                );
                                let box_rect = egui::Rect::from_center_size(
                                    sq_rect.center(),
                                    egui::vec2(9.0, 9.0),
                                );
                                if my_speak {
                                    ui.painter().rect_filled(box_rect, 0.0, CYBER_MINT);
                                } else {
                                    ui.painter().rect_stroke(
                                        box_rect,
                                        0.0,
                                        egui::Stroke::new(1.0_f32, RETRO_GRAY),
                                    );
                                }

                                ui.label(
                                    egui::RichText::new(format!("{} (ТЫ)", my_nick))
                                        .size(11.0)
                                        .strong()
                                        .color(if my_speak {
                                            egui::Color32::WHITE
                                        } else {
                                            RETRO_GRAY
                                        }),
                                );
                            });

                            let mut peers = self.state.room.peers.lock().unwrap();
                            let mut active_ids: Vec<u64> = peers
                                .values()
                                .filter(|p| p.connected)
                                .map(|p| p.id)
                                .collect();
                            active_ids.sort_unstable();

                            if active_ids.is_empty() {
                                ui.add_space(4.0);
                                ui.label(
                                    egui::RichText::new("Комната пуста — ждем остальных")
                                        .size(10.0)
                                        .color(RETRO_GRAY),
                                );
                            } else {
                                for pid in active_ids {
                                    if let Some(peer) = peers.get_mut(&pid) {
                                        ui.add_space(4.0);
                                        let is_talking =
                                            peer.last_spoke.elapsed() < Duration::from_millis(250);
                                        ui.horizontal(|ui| {
                                            let (sq_rect, _) = ui.allocate_exact_size(
                                                egui::vec2(12.0, 14.0),
                                                egui::Sense::hover(),
                                            );
                                            let box_rect = egui::Rect::from_center_size(
                                                sq_rect.center(),
                                                egui::vec2(9.0, 9.0),
                                            );
                                            if is_talking {
                                                ui.painter().rect_filled(box_rect, 0.0, CYBER_MINT);
                                            } else {
                                                ui.painter().rect_stroke(
                                                    box_rect,
                                                    0.0,
                                                    egui::Stroke::new(1.0_f32, RETRO_PINK),
                                                );
                                            }

                                            ui.add(
                                                egui::Label::new(
                                                    egui::RichText::new(&peer.name).size(11.0).color(
                                                        if is_talking {
                                                            egui::Color32::WHITE
                                                        } else {
                                                            RETRO_GRAY
                                                        },
                                                    ),
                                                )
                                                .truncate(),
                                            );

                                            ui.with_layout(
                                                egui::Layout::right_to_left(egui::Align::Center),
                                                |ui| {
                                                    retro_volume_bar(ui, &mut peer.volume);
                                                },
                                            );
                                        });
                                    }
                                }
                            }
                        });
                });
            }
        });
    }
}

fn main() -> eframe::Result<()> {
    if acquire_single_instance_or_focus() {
        return Ok(());
    }

    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_inner_size([396.0, 610.0])
            .with_resizable(false)
            .with_title(WINDOW_TITLE)
            .with_icon(Arc::new(generate_gg_icon())),
        ..Default::default()
    };

    let res = eframe::run_native(
        WINDOW_TITLE,
        options,
        Box::new(|cc| Ok(Box::new(GGVoiceApp::new(cc)))),
    );
    release_single_instance_lock();
    res
}