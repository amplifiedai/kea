use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static TEMP_NONCE: AtomicU64 = AtomicU64::new(0);

fn kea_bin() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_kea") {
        return PathBuf::from(path);
    }

    let mut exe = std::env::current_exe().expect("test executable path should be known");
    exe.pop();
    if exe.file_name().and_then(|name| name.to_str()) == Some("deps") {
        exe.pop();
    }
    exe.join("kea")
}

fn temp_source_path(prefix: &str) -> PathBuf {
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time should move forward")
        .as_nanos();
    let counter = TEMP_NONCE.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("{prefix}-{timestamp}-{counter}.kea"))
}

#[test]
fn kea_run_prints_hello_world_stdout() {
    let source = "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO.stdout(\"hello world\")\n";
    let path = temp_source_path("kea-cli-stdout");
    std::fs::write(&path, source).expect("temp source write should succeed");

    let output = Command::new(kea_bin())
        .arg("run")
        .arg(&path)
        .output()
        .expect("kea run should execute");

    let _ = std::fs::remove_file(path);

    assert_eq!(output.status.code(), Some(0));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("hello world"),
        "expected `hello world` in stdout, got: {stdout}"
    );
}

#[test]
fn kea_run_allocation_churn_smoke_does_not_crash() {
    let source = "struct Box\n  n: Int\n\nfn churn(i: Int, acc: Int) -> Int\n  if i == 0\n    acc\n  else\n    let b = Box { n: i }\n    churn(i - 1, acc + b.n - i)\n\nfn main() -> Int\n  churn(5000, 0)\n";
    let path = temp_source_path("kea-cli-churn");
    std::fs::write(&path, source).expect("temp source write should succeed");

    let output = Command::new(kea_bin())
        .arg("run")
        .arg(&path)
        .output()
        .expect("kea run should execute");

    let _ = std::fs::remove_file(path);

    assert_eq!(
        output.status.code(),
        Some(0),
        "expected churn program to complete without crash; stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
