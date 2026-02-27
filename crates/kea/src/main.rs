use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command as ProcessCommand;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use kea::{compile_file, emit_diagnostics, run_file};
use kea_codegen::CodegenMode;

static TEMP_NONCE: AtomicU64 = AtomicU64::new(0);

fn main() {
    if let Err(message) = run() {
        eprintln!("{message}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    let command = parse_cli(&args)?;

    match command {
        Command::Run { input } => {
            let result = run_file(&input)?;
            emit_diagnostics(&result.diagnostics);
            if result.exit_code != 0 {
                std::process::exit(result.exit_code);
            }
            Ok(())
        }
        Command::Build { input, output } => {
            let output = output.unwrap_or_else(|| default_build_output_path(&input));
            let result = compile_file(&input, CodegenMode::Aot)?;
            emit_diagnostics(&result.diagnostics);
            if result.object.is_empty() {
                return Err("AOT backend produced no object bytes".to_string());
            }
            if let Some(parent) = output.parent()
                && !parent.as_os_str().is_empty()
            {
                fs::create_dir_all(parent)
                    .map_err(|err| format!("failed to create output directory: {err}"))?;
            }
            if output.extension().and_then(|ext| ext.to_str()) == Some("o") {
                fs::write(&output, &result.object)
                    .map_err(|err| format!("failed to write `{}`: {err}", output.display()))?;
                println!(
                    "built object `{}` ({} bytes)",
                    output.display(),
                    result.object.len()
                );
            } else {
                link_object_bytes(&result.object, &output)?;
                println!("built executable `{}`", output.display());
            }
            Ok(())
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Command {
    Run {
        input: PathBuf,
    },
    Build {
        input: PathBuf,
        output: Option<PathBuf>,
    },
}

fn parse_cli(args: &[String]) -> Result<Command, String> {
    if args.len() < 3 {
        return Err(usage());
    }

    match args[1].as_str() {
        "run" => Ok(Command::Run {
            input: PathBuf::from(&args[2]),
        }),
        "build" => {
            let input = PathBuf::from(&args[2]);
            let mut output = None;

            let mut idx = 3;
            while idx < args.len() {
                match args[idx].as_str() {
                    "-o" | "--output" => {
                        if idx + 1 >= args.len() {
                            return Err("missing value for --output".to_string());
                        }
                        output = Some(PathBuf::from(&args[idx + 1]));
                        idx += 2;
                    }
                    unknown => {
                        return Err(format!("unknown argument `{unknown}`\n{}", usage()));
                    }
                }
            }

            Ok(Command::Build { input, output })
        }
        _ => Err(usage()),
    }
}

fn usage() -> String {
    "usage:\n  kea run <file.kea>\n  kea build <file.kea> [-o output|output.o]".to_string()
}

fn default_build_output_path(input: &Path) -> PathBuf {
    input.with_extension("")
}

fn link_object_bytes(object: &[u8], output: &Path) -> Result<(), String> {
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time should move forward")
        .as_nanos();
    let counter = TEMP_NONCE.fetch_add(1, Ordering::Relaxed);
    let temp_object = std::env::temp_dir().join(format!(
        "kea-build-{}-{timestamp}-{counter}.o",
        std::process::id()
    ));
    fs::write(&temp_object, object).map_err(|err| {
        format!(
            "failed to write temporary object `{}`: {err}",
            temp_object.display()
        )
    })?;

    let status = ProcessCommand::new("cc")
        .arg(&temp_object)
        .arg("-o")
        .arg(output)
        .status()
        .map_err(|err| format!("failed to invoke linker `cc`: {err}"))?;

    let _ = fs::remove_file(&temp_object);

    if !status.success() {
        return Err(format!(
            "linker failed for `{}` (exit status: {status})",
            output.display()
        ));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_build_with_output() {
        let args = vec![
            "kea".to_string(),
            "build".to_string(),
            "main.kea".to_string(),
            "-o".to_string(),
            "out/main.o".to_string(),
        ];

        let command = parse_cli(&args).expect("cli parse should succeed");
        assert_eq!(
            command,
            Command::Build {
                input: PathBuf::from("main.kea"),
                output: Some(PathBuf::from("out/main.o")),
            }
        );
    }

    #[test]
    fn default_build_output_path_strips_extension() {
        assert_eq!(
            default_build_output_path(Path::new("examples/hello.kea")),
            PathBuf::from("examples/hello")
        );
    }

    #[test]
    fn compile_and_execute_main_exit_code() {
        let source_path = write_temp_source("fn main() -> Int\n  9\n", "kea-cli-exec", "kea");

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 9);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_use_imported_module_function_exit_code() {
        let project_dir = temp_project_dir("kea-cli-project-import");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let math_path = src_dir.join("math.kea");
        std::fs::write(&math_path, "fn inc(x: Int) -> Int\n  x + 1\n")
            .expect("math module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(&app_path, "use Math\nfn main() -> Int\n  Math.inc(41)\n")
            .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_use_named_import_bare_call_exit_code() {
        let project_dir = temp_project_dir("kea-cli-project-import-named");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        std::fs::write(src_dir.join("math.kea"), "fn inc(x: Int) -> Int\n  x + 1\n")
            .expect("math module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(&app_path, "use Math.{inc}\nfn main() -> Int\n  inc(41)\n")
            .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_prelude_module_without_explicit_use_exit_code() {
        let project_dir = temp_project_dir("kea-cli-project-prelude");
        let src_dir = project_dir.join("src");
        let stdlib_dir = project_dir.join("stdlib");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");
        std::fs::create_dir_all(&stdlib_dir).expect("stdlib dir should be created");

        std::fs::write(
            stdlib_dir.join("prelude.kea"),
            "fn inc(x: Int) -> Int\n  x + 1\n",
        )
        .expect("prelude module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(&app_path, "fn main() -> Int\n  Prelude.inc(41)\n")
            .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_prelude_module_without_explicit_use_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-prelude");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(&app_path, "fn main() -> Int\n  Prelude.ping()\n")
            .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_io_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-io");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use IO\n\nfn main() -[IO]> Unit\n  IO.stdout(\"hello from stdlib io\")\n  IO.stderr(\"err from stdlib io\")\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 0);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_real_stdlib_io_read_write_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-io-read-write");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use IO\n\nfn main() -[IO]> Int\n  IO.write_file(\"tmp\", \"hello\")\n  let msg = IO.read_file(\"hello\")\n  IO.stdout(msg)\n  1\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_real_stdlib_clock_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-clock");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Clock\n\nfn main() -[Clock]> Int\n  if Clock.monotonic() > 0\n    1\n  else\n    0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_real_stdlib_rand_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-rand");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Rand\n\nfn main() -[Rand]> Int\n  Rand.seed(123)\n  if Rand.int() >= 0\n    1\n  else\n    0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_real_stdlib_net_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-net");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Net\n\nfn main() -[Net]> Int\n  let c = Net.connect(\"127.0.0.1:0\")\n  Net.send(c, \"ping\")\n  let n = Net.recv(c, 4)\n  if c >= 0 and n >= 0\n    1\n  else\n    0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_clock_now_direct_effect_exit_code() {
        let source_path = write_temp_source(
            "effect Clock\n  fn now() -> Int\n\nfn main() -[Clock]> Int\n  if Clock.now() > 0\n    1\n  else\n    0\n",
            "kea-cli-clock-now-direct",
            "kea",
        );

        let run = run_file(&source_path).expect("clock-now run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_clock_monotonic_direct_effect_exit_code() {
        let source_path = write_temp_source(
            "effect Clock\n  fn monotonic() -> Int\n\nfn main() -[Clock]> Int\n  if Clock.monotonic() > 0\n    1\n  else\n    0\n",
            "kea-cli-clock-monotonic-direct",
            "kea",
        );

        let run = run_file(&source_path).expect("clock-monotonic run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_rand_int_direct_effect_exit_code() {
        let source_path = write_temp_source(
            "effect Rand\n  fn int() -> Int\n  fn seed(seed: Int) -> Unit\n\nfn main() -[Rand]> Int\n  Rand.seed(123)\n  if Rand.int() >= 0\n    1\n  else\n    0\n",
            "kea-cli-rand-int-direct",
            "kea",
        );

        let run = run_file(&source_path).expect("rand-int run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_io_read_write_file_direct_effect_exit_code() {
        let source_path = write_temp_source(
            "effect IO\n  fn stdout(msg: String) -> Unit\n  fn write_file(path: String, data: String) -> Unit\n  fn read_file(path: String) -> String\n\nfn main() -[IO]> Int\n  IO.write_file(\"tmp\", \"hello\")\n  let msg = IO.read_file(\"hello\")\n  IO.stdout(msg)\n  1\n",
            "kea-cli-io-read-write-direct",
            "kea",
        );

        let run = run_file(&source_path).expect("io-read-write run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_net_direct_effect_exit_code() {
        let source_path = write_temp_source(
            "effect Net\n  fn connect(addr: String) -> Int\n  fn send(conn: Int, data: String) -> Unit\n  fn recv(conn: Int, size: Int) -> Int\n\nfn main() -[Net]> Int\n  let c = Net.connect(\"127.0.0.1:0\")\n  Net.send(c, \"ping\")\n  let n = Net.recv(c, 4)\n  if c >= 0 and n >= 0\n    1\n  else\n    0\n",
            "kea-cli-net-direct",
            "kea",
        );

        let run = run_file(&source_path).expect("net-direct run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_prelude_trait_unqualified_method_without_use_exit_code() {
        let project_dir = temp_project_dir("kea-cli-project-prelude-trait");
        let src_dir = project_dir.join("src");
        let stdlib_dir = project_dir.join("stdlib");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");
        std::fs::create_dir_all(&stdlib_dir).expect("stdlib dir should be created");

        std::fs::write(
            stdlib_dir.join("prelude.kea"),
            "trait Tinc a\n  fn tinc(x: a) -> a\n\nimpl Tinc for Int\n  fn tinc(x: Int) -> Int\n    x + 1\n",
        )
        .expect("prelude module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(&app_path, "fn main() -> Int\n  41.tinc()\n")
            .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_option_unwrap_or_intrinsic_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-integration");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Option\nuse Text\n\nfn main() -> Int\n  Option.unwrap_or(Some(39), 39) + Text.length(\"abc\")\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_option_predicates_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-option-preds");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Option\n\nfn main() -> Int\n  if Option.is_none(None) and Option.is_some(Some(42))\n    42\n  else\n    0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_result_helpers_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-result");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Result\n\nfn main() -> Int\n  if Result.unwrap_or(Ok(42), 0) == 42 and Result.is_ok(Ok(1)) and Result.is_err(Err(2))\n    42\n  else\n    0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_text_helpers_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-text");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Text\n\nfn main() -> Int\n  if Text.is_empty(\"\") and Text.non_empty(\"kea\")\n    42\n  else\n    0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_project_reports_list_module_blocked_until_heap_runtime() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-list-blocked");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(&app_path, "use List\n\nfn main() -> Int\n  0\n")
            .expect("app module write should succeed");

        let err =
            run_file(&app_path).expect_err("List stdlib module should remain blocked for now");
        assert!(
            err.contains("module `List` not found"),
            "expected missing-List module error, got: {err}"
        );

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_int_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-numeric");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Int\n\nfn main() -> Int\n  Int.clamp(-5, 0, 10) + Int.abs(-42)\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_order_module_qualified_constructor_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-order-qual");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Order\n\nfn main() -> Int\n  let value = Order.Less\n  case value\n    Order.Less -> 1\n    _ -> 0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_order_helpers_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-order-helpers");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Order\n\nfn main() -> Int\n  if Order.is_less(Order.compare_int(1, 2)) and Order.is_equal(Order.compare_int(3, 3)) and Order.is_greater(Order.compare_int(9, 4))\n    42\n  else\n    0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_float_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-float");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Float\n\nfn main() -> Int\n  if Float.fabs(-42.5) == 42.5\n    42\n  else\n    0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_trait_modules_import_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-traits");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Eq\nuse Ord\nuse Show\n\nfn main() -> Int\n  0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 0);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_project_accepts_unqualified_prelude_reexported_type_names() {
        let project_dir = temp_project_dir("kea-cli-project-prelude-reexports");
        let src_dir = project_dir.join("src");
        let stdlib_dir = project_dir.join("stdlib");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");
        std::fs::create_dir_all(&stdlib_dir).expect("stdlib dir should be created");

        std::fs::write(stdlib_dir.join("prelude.kea"), "use Order\n")
            .expect("prelude module write should succeed");
        std::fs::write(
            stdlib_dir.join("order.kea"),
            "type Ordering = Less | Equal | Greater\n",
        )
        .expect("order module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "fn identity(o: Ordering) -> Ordering\n  o\n\nfn main() -> Int\n  0\n",
        )
        .expect("app module write should succeed");

        let _compiled = kea::compile_project(&app_path).expect("project compile should succeed");

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_project_rejects_bare_call_without_named_import() {
        let project_dir = temp_project_dir("kea-cli-project-import-scope");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        std::fs::write(src_dir.join("math.kea"), "fn inc(x: Int) -> Int\n  x + 1\n")
            .expect("math module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(&app_path, "use Math\nfn main() -> Int\n  inc(41)\n")
            .expect("app module write should succeed");

        let err = run_file(&app_path).expect_err("bare import should require named use");
        assert!(
            err.contains("undefined variable `inc`"),
            "expected undefined variable diagnostic, got: {err}"
        );

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_project_tracks_module_item_visibility_metadata() {
        let project_dir = temp_project_dir("kea-cli-project-visibility-metadata");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        std::fs::write(
            src_dir.join("math.kea"),
            "pub fn inc(x: Int) -> Int\n  x + 1\n\nfn hidden(x: Int) -> Int\n  x + 2\n",
        )
        .expect("math module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(&app_path, "use Math\nfn main() -> Int\n  Math.inc(41)\n")
            .expect("app module write should succeed");

        let compiled = kea::compile_project(&app_path).expect("project compile should succeed");
        assert_eq!(
            compiled.type_env.module_item_visibility("Math", "inc"),
            Some(true),
            "expected public visibility metadata for Math.inc",
        );
        assert_eq!(
            compiled.type_env.module_item_visibility("Math", "hidden"),
            Some(false),
            "expected private visibility metadata for Math.hidden",
        );
        let module_struct = compiled
            .type_env
            .module_struct_info("Math")
            .expect("expected module struct metadata for Math");
        assert_eq!(module_struct.name, "Math");
        assert!(
            !module_struct.merged_with_named_type,
            "Math module should not report same-name type merge",
        );
        let inherent_methods = compiled.type_env.inherent_methods_for_type("Math");
        assert!(
            inherent_methods.iter().any(|name| name == "inc"),
            "expected Math.inc to be registered as an inherent module method",
        );
        assert!(
            inherent_methods.iter().any(|name| name == "hidden"),
            "expected Math.hidden to be registered as an inherent module method",
        );

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_project_marks_same_name_module_type_merge() {
        let project_dir = temp_project_dir("kea-cli-project-module-struct-merge");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        std::fs::write(
            src_dir.join("list.kea"),
            "type List = Empty | Item(Int)\n\nfn size(_ self: List) -> Int\n  1\n",
        )
        .expect("list module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(&app_path, "use List\nfn main() -> Int\n  0\n")
            .expect("app module write should succeed");

        let compiled = kea::compile_project(&app_path).expect("project compile should succeed");
        let module_struct = compiled
            .type_env
            .module_struct_info("List")
            .expect("expected module struct metadata for List");
        assert_eq!(module_struct.name, "List");
        assert!(
            module_struct.merged_with_named_type,
            "List module should mark same-name type merge",
        );
        let inherent_methods = compiled.type_env.inherent_methods_for_type("List");
        assert!(
            inherent_methods.iter().any(|name| name == "size"),
            "expected List.size to be registered as an inherent module method",
        );

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_use_module_unqualified_ums_for_same_name_module_struct_method() {
        let project_dir = temp_project_dir("kea-cli-project-module-struct-ums");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        std::fs::write(
            src_dir.join("list.kea"),
            "type List = Empty | Item(Int)\n\nfn size(xs: List) -> Int\n  case xs\n    Empty -> 0\n    Item(n) -> n + 8\n",
        )
        .expect("list module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use List\nfn main() -> Int\n  let xs = Item(1)\n  xs.size()\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 9);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_project_reports_circular_module_imports() {
        let project_dir = temp_project_dir("kea-cli-project-cycle");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(&app_path, "use A\nfn main() -> Int\n  A.value()\n")
            .expect("app module write should succeed");
        std::fs::write(
            src_dir.join("a.kea"),
            "use B\nfn value() -> Int\n  B.other()\n",
        )
        .expect("module A write should succeed");
        std::fs::write(
            src_dir.join("b.kea"),
            "use A\nfn other() -> Int\n  A.value()\n",
        )
        .expect("module B write should succeed");

        let err = run_file(&app_path).expect_err("circular import should fail");
        assert!(
            err.contains("circular module import detected"),
            "expected circular import diagnostic, got: {err}"
        );

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[derive(Clone, Copy, Debug)]
    enum MatrixCallForm {
        DirectQualified,
        UmsUnqualified,
        UmsQualified,
    }

    #[derive(Clone, Copy, Debug)]
    enum MatrixImportState {
        NotImported,
        UseModule,
        UseModuleNamed,
        Prelude,
    }

    #[derive(Clone, Copy, Debug)]
    enum MatrixModuleRelation {
        SameModule,
        CrossModule,
    }

    fn matrix_inherent_expected(
        call_form: MatrixCallForm,
        import_state: MatrixImportState,
        relation: MatrixModuleRelation,
    ) -> bool {
        if matches!(relation, MatrixModuleRelation::SameModule) {
            return true;
        }
        match call_form {
            MatrixCallForm::DirectQualified | MatrixCallForm::UmsQualified => {
                !matches!(import_state, MatrixImportState::NotImported)
            }
            MatrixCallForm::UmsUnqualified => {
                matches!(import_state, MatrixImportState::UseModuleNamed)
            }
        }
    }

    fn matrix_trait_expected(
        call_form: MatrixCallForm,
        import_state: MatrixImportState,
        relation: MatrixModuleRelation,
    ) -> bool {
        if matches!(relation, MatrixModuleRelation::SameModule) {
            return true;
        }
        match call_form {
            MatrixCallForm::DirectQualified | MatrixCallForm::UmsQualified => {
                !matches!(import_state, MatrixImportState::NotImported)
            }
            MatrixCallForm::UmsUnqualified => {
                matches!(
                    import_state,
                    MatrixImportState::UseModule
                        | MatrixImportState::UseModuleNamed
                        | MatrixImportState::Prelude
                )
            }
        }
    }

    fn matrix_same_name_module_struct_expected(
        call_form: MatrixCallForm,
        import_state: MatrixImportState,
        relation: MatrixModuleRelation,
    ) -> bool {
        if matches!(relation, MatrixModuleRelation::SameModule) {
            return true;
        }
        match call_form {
            MatrixCallForm::DirectQualified | MatrixCallForm::UmsQualified => {
                !matches!(import_state, MatrixImportState::NotImported)
            }
            MatrixCallForm::UmsUnqualified => {
                matches!(
                    import_state,
                    MatrixImportState::UseModule
                        | MatrixImportState::UseModuleNamed
                        | MatrixImportState::Prelude
                )
            }
        }
    }

    fn matrix_error_looks_like_resolution(err: &str) -> bool {
        err.contains("undefined variable")
            || err.contains("unknown module")
            || err.contains("has no function")
            || err.contains("unresolved qualified call target")
    }

    #[test]
    fn resolution_matrix_inherent_methods() {
        let call_forms = [
            MatrixCallForm::DirectQualified,
            MatrixCallForm::UmsUnqualified,
            MatrixCallForm::UmsQualified,
        ];
        let import_states = [
            MatrixImportState::NotImported,
            MatrixImportState::UseModule,
            MatrixImportState::UseModuleNamed,
            MatrixImportState::Prelude,
        ];
        let relations = [
            MatrixModuleRelation::SameModule,
            MatrixModuleRelation::CrossModule,
        ];

        for relation in relations {
            for import_state in import_states {
                for call_form in call_forms {
                    let expect_success =
                        matrix_inherent_expected(call_form, import_state, relation);
                    let project_dir = temp_project_dir("kea-cli-resolution-matrix-inherent");
                    let src_dir = project_dir.join("src");
                    let stdlib_dir = project_dir.join("stdlib");
                    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
                    std::fs::create_dir_all(&stdlib_dir).expect("stdlib dir should be created");

                    let mut imports = Vec::new();
                    let mut app_defs = Vec::new();
                    let module_qualifier = match relation {
                        MatrixModuleRelation::SameModule => {
                            app_defs.push("fn inc(x: Int) -> Int\n  x + 1".to_string());
                            "App".to_string()
                        }
                        MatrixModuleRelation::CrossModule => match import_state {
                            MatrixImportState::Prelude => {
                                std::fs::write(
                                    stdlib_dir.join("prelude.kea"),
                                    "fn inc(x: Int) -> Int\n  x + 1\n",
                                )
                                .expect("prelude write should succeed");
                                "Prelude".to_string()
                            }
                            MatrixImportState::NotImported => {
                                std::fs::write(
                                    src_dir.join("core.kea"),
                                    "fn inc(x: Int) -> Int\n  x + 1\n",
                                )
                                .expect("core write should succeed");
                                "Core".to_string()
                            }
                            MatrixImportState::UseModule => {
                                std::fs::write(
                                    src_dir.join("core.kea"),
                                    "fn inc(x: Int) -> Int\n  x + 1\n",
                                )
                                .expect("core write should succeed");
                                imports.push("use Core".to_string());
                                "Core".to_string()
                            }
                            MatrixImportState::UseModuleNamed => {
                                std::fs::write(
                                    src_dir.join("core.kea"),
                                    "fn inc(x: Int) -> Int\n  x + 1\n",
                                )
                                .expect("core write should succeed");
                                imports.push("use Core.{inc}".to_string());
                                "Core".to_string()
                            }
                        },
                    };

                    let call_expr = match call_form {
                        MatrixCallForm::DirectQualified => format!("{module_qualifier}.inc(41)"),
                        MatrixCallForm::UmsUnqualified => "41.inc()".to_string(),
                        MatrixCallForm::UmsQualified => format!("41.{module_qualifier}.inc()"),
                    };

                    let mut app_source = String::new();
                    if !imports.is_empty() {
                        app_source.push_str(&imports.join("\n"));
                        app_source.push('\n');
                    }
                    if !app_defs.is_empty() {
                        app_source.push_str(&app_defs.join("\n\n"));
                        app_source.push_str("\n\n");
                    }
                    app_source.push_str("fn main() -> Int\n  ");
                    app_source.push_str(&call_expr);
                    app_source.push('\n');
                    let app_path = src_dir.join("app.kea");
                    std::fs::write(&app_path, app_source).expect("app write should succeed");

                    let run = run_file(&app_path);
                    if expect_success {
                        let run = run.unwrap_or_else(|err| {
                            panic!(
                                "expected success for relation={relation:?}, import={import_state:?}, call={call_form:?}, got error: {err}"
                            )
                        });
                        assert_eq!(
                            run.exit_code, 42,
                            "unexpected exit code for relation={relation:?}, import={import_state:?}, call={call_form:?}"
                        );
                    } else {
                        let err = run.expect_err("expected resolution failure");
                        assert!(
                            matrix_error_looks_like_resolution(&err),
                            "expected resolution-style error for relation={relation:?}, import={import_state:?}, call={call_form:?}; got: {err}"
                        );
                    }

                    let _ = std::fs::remove_dir_all(project_dir);
                }
            }
        }
    }

    #[test]
    fn resolution_matrix_trait_methods() {
        let call_forms = [
            MatrixCallForm::DirectQualified,
            MatrixCallForm::UmsUnqualified,
            MatrixCallForm::UmsQualified,
        ];
        let import_states = [
            MatrixImportState::NotImported,
            MatrixImportState::UseModule,
            MatrixImportState::UseModuleNamed,
            MatrixImportState::Prelude,
        ];
        let relations = [
            MatrixModuleRelation::SameModule,
            MatrixModuleRelation::CrossModule,
        ];

        for relation in relations {
            for import_state in import_states {
                for call_form in call_forms {
                    let expect_success = matrix_trait_expected(call_form, import_state, relation);
                    let project_dir = temp_project_dir("kea-cli-resolution-matrix-trait");
                    let src_dir = project_dir.join("src");
                    let stdlib_dir = project_dir.join("stdlib");
                    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
                    std::fs::create_dir_all(&stdlib_dir).expect("stdlib dir should be created");

                    let mut imports = Vec::new();
                    let mut app_defs = Vec::new();
                    match relation {
                        MatrixModuleRelation::SameModule => {
                            app_defs.push(
                                "trait Tinc a\n  fn tinc(x: a) -> a\n\nimpl Tinc for Int\n  fn tinc(x: Int) -> Int\n    x + 1"
                                    .to_string(),
                            );
                        }
                        MatrixModuleRelation::CrossModule => match import_state {
                            MatrixImportState::Prelude => {
                                std::fs::write(
                                    stdlib_dir.join("prelude.kea"),
                                    "trait Tinc a\n  fn tinc(x: a) -> a\n\nimpl Tinc for Int\n  fn tinc(x: Int) -> Int\n    x + 1\n",
                                )
                                .expect("prelude write should succeed");
                            }
                            MatrixImportState::NotImported => {
                                std::fs::write(
                                    src_dir.join("tinc.kea"),
                                    "trait Tinc a\n  fn tinc(x: a) -> a\n\nimpl Tinc for Int\n  fn tinc(x: Int) -> Int\n    x + 1\n",
                                )
                                .expect("tinc write should succeed");
                            }
                            MatrixImportState::UseModule => {
                                std::fs::write(
                                    src_dir.join("tinc.kea"),
                                    "trait Tinc a\n  fn tinc(x: a) -> a\n\nimpl Tinc for Int\n  fn tinc(x: Int) -> Int\n    x + 1\n",
                                )
                                .expect("tinc write should succeed");
                                imports.push("use Tinc".to_string());
                            }
                            MatrixImportState::UseModuleNamed => {
                                std::fs::write(
                                    src_dir.join("tinc.kea"),
                                    "trait Tinc a\n  fn tinc(x: a) -> a\n\nimpl Tinc for Int\n  fn tinc(x: Int) -> Int\n    x + 1\n",
                                )
                                .expect("tinc write should succeed");
                                imports.push("use Tinc.{tinc}".to_string());
                            }
                        },
                    }

                    let call_expr = match call_form {
                        MatrixCallForm::DirectQualified => "Tinc.tinc(41)".to_string(),
                        MatrixCallForm::UmsUnqualified => "41.tinc()".to_string(),
                        MatrixCallForm::UmsQualified => "41.Tinc.tinc()".to_string(),
                    };

                    let mut app_source = String::new();
                    if !imports.is_empty() {
                        app_source.push_str(&imports.join("\n"));
                        app_source.push('\n');
                    }
                    if !app_defs.is_empty() {
                        app_source.push_str(&app_defs.join("\n\n"));
                        app_source.push_str("\n\n");
                    }
                    app_source.push_str("fn main() -> Int\n  ");
                    app_source.push_str(&call_expr);
                    app_source.push('\n');
                    let app_path = src_dir.join("app.kea");
                    std::fs::write(&app_path, app_source).expect("app write should succeed");

                    let run = run_file(&app_path);
                    if expect_success {
                        let run = run.unwrap_or_else(|err| {
                            panic!(
                                "expected success for relation={relation:?}, import={import_state:?}, call={call_form:?}, got error: {err}"
                            )
                        });
                        assert_eq!(
                            run.exit_code, 42,
                            "unexpected exit code for relation={relation:?}, import={import_state:?}, call={call_form:?}"
                        );
                    } else {
                        let err = run.expect_err("expected resolution failure");
                        assert!(
                            matrix_error_looks_like_resolution(&err),
                            "expected resolution-style error for relation={relation:?}, import={import_state:?}, call={call_form:?}; got: {err}"
                        );
                    }

                    let _ = std::fs::remove_dir_all(project_dir);
                }
            }
        }
    }

    #[test]
    fn resolution_matrix_same_name_module_struct_methods() {
        let call_forms = [
            MatrixCallForm::DirectQualified,
            MatrixCallForm::UmsUnqualified,
            MatrixCallForm::UmsQualified,
        ];
        let import_states = [
            MatrixImportState::NotImported,
            MatrixImportState::UseModule,
            MatrixImportState::UseModuleNamed,
            MatrixImportState::Prelude,
        ];
        let relations = [
            MatrixModuleRelation::SameModule,
            MatrixModuleRelation::CrossModule,
        ];

        for relation in relations {
            for import_state in import_states {
                for call_form in call_forms {
                    let expect_success =
                        matrix_same_name_module_struct_expected(call_form, import_state, relation);
                    let project_dir = temp_project_dir("kea-cli-resolution-matrix-module-struct");
                    let src_dir = project_dir.join("src");
                    let stdlib_dir = project_dir.join("stdlib");
                    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
                    std::fs::create_dir_all(&stdlib_dir).expect("stdlib dir should be created");

                    let mut imports = Vec::new();
                    let mut app_defs = Vec::new();
                    let list_module_source = "type List = Empty | Item(Int)\n\nfn size(xs: List) -> Int\n  case xs\n    Empty -> 0\n    Item(n) -> n + 8\n";
                    let app_module_source = "type App = Empty | Item(Int)\n\nfn size(xs: App) -> Int\n  case xs\n    Empty -> 0\n    Item(n) -> n + 8\n";
                    let module_qualifier = match relation {
                        MatrixModuleRelation::SameModule => "App".to_string(),
                        MatrixModuleRelation::CrossModule => "List".to_string(),
                    };
                    match relation {
                        MatrixModuleRelation::SameModule => {
                            app_defs.push(app_module_source.to_string());
                        }
                        MatrixModuleRelation::CrossModule => match import_state {
                            MatrixImportState::Prelude => {
                                std::fs::write(stdlib_dir.join("list.kea"), list_module_source)
                                    .expect("list write should succeed");
                                std::fs::write(stdlib_dir.join("prelude.kea"), "use List\n")
                                    .expect("prelude write should succeed");
                            }
                            MatrixImportState::NotImported => {
                                std::fs::write(src_dir.join("list.kea"), list_module_source)
                                    .expect("list write should succeed");
                            }
                            MatrixImportState::UseModule => {
                                std::fs::write(src_dir.join("list.kea"), list_module_source)
                                    .expect("list write should succeed");
                                imports.push("use List".to_string());
                            }
                            MatrixImportState::UseModuleNamed => {
                                std::fs::write(src_dir.join("list.kea"), list_module_source)
                                    .expect("list write should succeed");
                                imports.push("use List.{size}".to_string());
                            }
                        },
                    }

                    let call_block = match call_form {
                        MatrixCallForm::DirectQualified => {
                            format!("{module_qualifier}.size(Item(41))")
                        }
                        MatrixCallForm::UmsUnqualified => {
                            "let xs = Item(41)\nxs.size()".to_string()
                        }
                        MatrixCallForm::UmsQualified => {
                            format!("let xs = Item(41)\nxs.{module_qualifier}.size()")
                        }
                    };

                    let mut app_source = String::new();
                    if !imports.is_empty() {
                        app_source.push_str(&imports.join("\n"));
                        app_source.push('\n');
                    }
                    if !app_defs.is_empty() {
                        app_source.push_str(&app_defs.join("\n\n"));
                        app_source.push_str("\n\n");
                    }
                    app_source.push_str("fn main() -> Int\n  ");
                    app_source.push_str(&call_block.replace('\n', "\n  "));
                    app_source.push('\n');
                    let app_path = src_dir.join("app.kea");
                    std::fs::write(&app_path, app_source).expect("app write should succeed");

                    let run = run_file(&app_path);
                    if expect_success {
                        let run = run.unwrap_or_else(|err| {
                            panic!(
                                "expected success for relation={relation:?}, import={import_state:?}, call={call_form:?}, got error: {err}"
                            )
                        });
                        assert_eq!(
                            run.exit_code, 49,
                            "unexpected exit code for relation={relation:?}, import={import_state:?}, call={call_form:?}"
                        );
                    } else {
                        let err = run.expect_err("expected resolution failure");
                        assert!(
                            matrix_error_looks_like_resolution(&err),
                            "expected resolution-style error for relation={relation:?}, import={import_state:?}, call={call_form:?}; got: {err}"
                        );
                    }

                    let _ = std::fs::remove_dir_all(project_dir);
                }
            }
        }
    }

    #[test]
    fn compile_and_execute_io_stdout_unit_main_exit_code() {
        let source_path = write_temp_source(
            "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO.stdout(\"hello world\")\n",
            "kea-cli-io-stdout",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 0);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_io_stdout_string_concat_exit_code() {
        let source_path = write_temp_source(
            "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO.stdout(\"hello \" ++ \"world\")\n",
            "kea-cli-io-stdout-concat",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 0);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_io_stderr_unit_main_exit_code() {
        let source_path = write_temp_source(
            "effect IO\n  fn stderr(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO.stderr(\"hello err\")\n",
            "kea-cli-io-stderr",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 0);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_intrinsic_strlen_exit_code() {
        let source_path = write_temp_source(
            "@intrinsic(\"strlen\")\nfn string_len(s: String) -> Int\n  0\n\nfn main() -> Int\n  string_len(\"hello\")\n",
            "kea-cli-intrinsic-strlen",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 5);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_build_and_execute_aot_payload_constructor_case_exit_code() {
        let source_path = write_temp_source(
            "type Flag = Yep(Int) | Nope\n\nfn main() -> Int\n  case Yep(1 + 6)\n    Yep(n) -> n\n    Nope -> 0\n",
            "kea-cli-aot-sum-case",
            "kea",
        );
        let output_path = temp_artifact_path("kea-cli-aot-sum-case", "bin");

        let compiled =
            compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
        link_object_bytes(&compiled.object, &output_path).expect("link should work");

        let status = std::process::Command::new(&output_path)
            .status()
            .expect("aot executable should run");
        assert_eq!(status.code(), Some(7));

        let _ = std::fs::remove_file(source_path);
        let _ = std::fs::remove_file(output_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_build_and_execute_aot_io_stdout_unit_main_exit_code() {
        let source_path = write_temp_source(
            "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO.stdout(\"hello aot\")\n",
            "kea-cli-aot-io-stdout",
            "kea",
        );
        let output_path = temp_artifact_path("kea-cli-aot-io-stdout", "bin");

        let compiled =
            compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
        link_object_bytes(&compiled.object, &output_path).expect("link should work");

        let output = std::process::Command::new(&output_path)
            .output()
            .expect("aot executable should run");
        assert_eq!(output.status.code(), Some(0));
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains("hello aot"),
            "expected stdout to contain greeting, got `{stdout}`"
        );

        let _ = std::fs::remove_file(source_path);
        let _ = std::fs::remove_file(output_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_build_and_execute_aot_io_stdout_concat_exit_code() {
        let source_path = write_temp_source(
            "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO.stdout(\"hello \" ++ \"aot\")\n",
            "kea-cli-aot-io-stdout-concat",
            "kea",
        );
        let output_path = temp_artifact_path("kea-cli-aot-io-stdout-concat", "bin");

        let compiled =
            compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
        link_object_bytes(&compiled.object, &output_path).expect("link should work");

        let output = std::process::Command::new(&output_path)
            .output()
            .expect("aot executable should run");
        assert_eq!(output.status.code(), Some(0));
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains("hello aot"),
            "expected stdout to contain concat greeting, got `{stdout}`"
        );

        let _ = std::fs::remove_file(source_path);
        let _ = std::fs::remove_file(output_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_build_and_execute_aot_io_stderr_unit_main_exit_code() {
        let source_path = write_temp_source(
            "effect IO\n  fn stderr(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO.stderr(\"hello aot err\")\n",
            "kea-cli-aot-io-stderr",
            "kea",
        );
        let output_path = temp_artifact_path("kea-cli-aot-io-stderr", "bin");

        let compiled =
            compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
        link_object_bytes(&compiled.object, &output_path).expect("link should work");

        let output = std::process::Command::new(&output_path)
            .output()
            .expect("aot executable should run");
        assert_eq!(output.status.code(), Some(0));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("hello aot err"),
            "expected stderr to contain message, got `{stderr}`"
        );

        let _ = std::fs::remove_file(source_path);
        let _ = std::fs::remove_file(output_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_jit_and_aot_exit_code_parity_corpus() {
        let cases = [
            ("fn main() -> Int\n  let x = 40\n  x + 2\n", 42),
            (
                "record User\n  age: Int\n\nfn main() -> Int\n  let u = User { age: 41 }\n  u.age + 1\n",
                42,
            ),
            (
                "type Maybe a = Just(a) | Nothing\n\nfn main() -> Int\n  case Just(41)\n    Just(n) -> n + 1\n    Nothing -> 0\n",
                42,
            ),
            (
                "fn apply(f: fn(Int) -> Int, x: Int) -> Int\n  f(x)\n\nfn main() -> Int\n  apply(|x| -> x + 1, 41)\n",
                42,
            ),
            (
                "effect Fail\n  fn fail(err: Int) -> Never\n\nfn f() -[Fail Int]> Int\n  fail 7\n\nfn main() -> Int\n  let r = catch f()\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
                7,
            ),
            ("fn main() -> Int\n  5.shift_left(3) + 2\n", 42),
        ];

        for (idx, (source, expected_exit)) in cases.iter().enumerate() {
            let name = format!("kea-cli-jit-aot-parity-{idx}");
            let source_path = write_temp_source(source, &name, "kea");

            let jit = run_file(&source_path).unwrap_or_else(|err| {
                panic!("jit run should succeed for parity case {idx}: {err}")
            });
            assert_eq!(
                jit.exit_code, *expected_exit,
                "jit exit mismatch for parity case {idx}"
            );

            let output_path = temp_artifact_path(&name, "bin");
            let compiled = compile_file(&source_path, CodegenMode::Aot).unwrap_or_else(|err| {
                panic!("aot compile should work for parity case {idx}: {err}")
            });
            link_object_bytes(&compiled.object, &output_path).expect("link should work");

            let status = std::process::Command::new(&output_path)
                .status()
                .expect("aot executable should run");
            assert_eq!(
                status.code(),
                Some(*expected_exit),
                "aot exit mismatch for parity case {idx}"
            );

            let _ = std::fs::remove_file(source_path);
            let _ = std::fs::remove_file(output_path);
        }
    }

    #[test]
    fn compile_and_execute_bitwise_and_method_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  42.bit_and(15)\n",
            "kea-cli-bitwise-and",
            "kea",
        );

        let run = run_file(&source_path).expect("bitwise-and run should succeed");
        assert_eq!(run.exit_code, 10);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_shift_left_method_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  1.shift_left(3)\n",
            "kea-cli-bitwise-shift-left",
            "kea",
        );

        let run = run_file(&source_path).expect("shift-left run should succeed");
        assert_eq!(run.exit_code, 8);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_bit_not_method_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  255.bit_not()\n",
            "kea-cli-bitwise-not",
            "kea",
        );

        let run = run_file(&source_path).expect("bit-not run should succeed");
        assert_eq!(run.exit_code, -256);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_shift_right_unsigned_method_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  16.shift_right_unsigned(2)\n",
            "kea-cli-bitwise-shift-right-u",
            "kea",
        );

        let run = run_file(&source_path).expect("shift-right-unsigned run should succeed");
        assert_eq!(run.exit_code, 4);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_higher_order_function_pointer_exit_code() {
        let source_path = write_temp_source(
            "fn inc(n: Int) -> Int\n  n + 1\n\nfn apply_twice(f: fn(Int) -> Int, x: Int) -> Int\n  f(f(x))\n\nfn main() -> Int\n  apply_twice(inc, 41)\n",
            "kea-cli-hof-fn-pointer",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 43);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_higher_order_lambda_argument_exit_code() {
        let source_path = write_temp_source(
            "fn apply(f: fn(Int) -> Int, x: Int) -> Int\n  f(x)\n\nfn main() -> Int\n  apply(|x| -> x + 1, 41)\n",
            "kea-cli-hof-lambda-arg",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_direct_lambda_call_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  (|x| -> x + 1)(41)\n",
            "kea-cli-direct-lambda-call",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_tail_recursive_countdown_exit_code() {
        let source_path = write_temp_source(
            "fn count(n: Int, acc: Int) -> Int\n  if n == 0\n    acc\n  else\n    count(n - 1, acc + 1)\n\nfn main() -> Int\n  count(100000, 0)\n",
            "kea-cli-tail-recursive-countdown",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 100000);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_tail_recursive_factorial_mod_exit_code() {
        let source_path = write_temp_source(
            "fn fact_mod(n: Int, acc: Int) -> Int\n  if n == 0\n    acc\n  else\n    fact_mod(n - 1, (acc * n) % 1000000007)\n\nfn main() -> Int\n  fact_mod(100000, 1)\n",
            "kea-cli-tail-recursive-factorial-mod",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 457992974);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_refcount_allocation_churn_exit_code() {
        let source_path = write_temp_source(
            "record Box\n  n: Int\n\nfn churn(i: Int, acc: Int) -> Int\n  if i == 0\n    acc\n  else\n    let b = Box { n: i }\n    churn(i - 1, acc + b.n - i)\n\nfn main() -> Int\n  churn(5000, 0)\n",
            "kea-cli-refcount-churn",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 0);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_emits_release_ops_for_allocation_churn_program() {
        let source_path = write_temp_source(
            "record Box\n  n: Int\n\nfn churn(i: Int, acc: Int) -> Int\n  if i == 0\n    acc\n  else\n    let b = Box { n: i }\n    churn(i - 1, acc + b.n - i)\n\nfn main() -> Int\n  churn(1024, 0)\n",
            "kea-cli-refcount-stats",
            "kea",
        );

        let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
        let alloc_count: usize = compiled
            .stats
            .per_function
            .iter()
            .map(|f| f.alloc_count)
            .sum();
        let release_count: usize = compiled
            .stats
            .per_function
            .iter()
            .map(|f| f.release_count)
            .sum();

        assert!(alloc_count > 0, "expected allocation ops in churn program");
        assert!(
            release_count > 0,
            "expected release ops in churn program, stats: {:?}",
            compiled.stats
        );
        assert!(
            release_count >= alloc_count.saturating_sub(2),
            "expected release count to track allocations closely, alloc={alloc_count}, release={release_count}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_local_function_alias_call_exit_code() {
        let source_path = write_temp_source(
            "fn inc(n: Int) -> Int\n  n + 1\n\nfn main() -> Int\n  let g = inc\n  g(41)\n",
            "kea-cli-local-fn-alias",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_let_bound_lambda_call_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let f = |x| -> x + 1\n  f(41)\n",
            "kea-cli-let-lambda-call",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_returned_capturing_lambda_call_exit_code() {
        let source_path = write_temp_source(
            "fn make_adder(y: Int) -> fn(Int) -> Int\n  |x| -> x + y\n\nfn main() -> Int\n  let add2 = make_adder(2)\n  add2(40)\n",
            "kea-cli-returned-capturing-lambda-call",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_immediate_capturing_lambda_call_exit_code() {
        let source_path = write_temp_source(
            "fn make_adder(y: Int) -> fn(Int) -> Int\n  |x| -> x + y\n\nfn main() -> Int\n  make_adder(2)(40)\n",
            "kea-cli-immediate-capturing-lambda-call",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_escaping_capturing_lambda_value_exit_code() {
        let source_path = write_temp_source(
            "fn apply(f: fn(Int) -> Int, x: Int) -> Int\n  f(x)\n\nfn make_adder(y: Int) -> fn(Int) -> Int\n  |x| -> x + y\n\nfn main() -> Int\n  apply(make_adder(2), 40)\n",
            "kea-cli-escaping-capturing-lambda",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_fail_only_main_ok_path_exit_code() {
        let source_path = write_temp_source(
            "effect Fail\n  fn fail(err: Int) -> Never\n\nfn main() -[Fail]> Int\n  12\n",
            "kea-cli-fail-main-ok",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 12);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_fail_only_main_err_path_reports_unhandled_fail() {
        let source_path = write_temp_source(
            "effect Fail\n  fn fail(err: Int) -> Never\n\nfn main() -[Fail Int]> Int\n  fail 9\n",
            "kea-cli-fail-main-err",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should report unhandled fail");
        assert!(
            err.contains("unhandled Fail"),
            "expected unhandled Fail error, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_catch_fail_result_case_exit_code() {
        let source_path = write_temp_source(
            "effect Fail\n  fn fail(err: Int) -> Never\n\nfn f() -[Fail Int]> Int\n  fail 7\n\nfn main() -> Int\n  let r = catch f()\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
            "kea-cli-catch-fail-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_catch_ok_result_case_exit_code() {
        let source_path = write_temp_source(
            "effect Fail\n  fn fail(err: Int) -> Never\n\nfn f() -[Fail Int]> Int\n  5\n\nfn main() -> Int\n  let r = catch f()\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
            "kea-cli-catch-ok-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 5);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_catch_higher_order_fail_parameter_err_exit_code() {
        let source_path = write_temp_source(
            "effect Fail\n  fn fail(err: Int) -> Never\n\nfn call_with_catch(f: fn() -[Fail Int]> Int) -> Result(Int, Int)\n  catch f()\n\nfn boom() -[Fail Int]> Int\n  fail 7\n\nfn main() -> Int\n  let r = call_with_catch(boom)\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
            "kea-cli-catch-higher-order-fail-err",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_catch_higher_order_fail_parameter_ok_exit_code() {
        let source_path = write_temp_source(
            "effect Fail\n  fn fail(err: Int) -> Never\n\nfn call_with_catch(f: fn() -[Fail Int]> Int) -> Result(Int, Int)\n  catch f()\n\nfn ok() -[Fail Int]> Int\n  9\n\nfn main() -> Int\n  let r = call_with_catch(ok)\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
            "kea-cli-catch-higher-order-fail-ok",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 9);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_try_sugar_fail_path_exit_code() {
        let source_path = write_temp_source(
            "effect Fail\n  fn fail(err: Int) -> Never\n\nfn step(ok: Bool) -> Result(Int, Int)\n  if ok then Ok(41) else Err(7)\n\nfn run(ok: Bool) -[Fail Int]> Int\n  step(ok)?\n\nfn main() -> Int\n  let r = catch run(false)\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
            "kea-cli-try-sugar-fail",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_try_sugar_ok_path_exit_code() {
        let source_path = write_temp_source(
            "effect Fail\n  fn fail(err: Int) -> Never\n\nfn step(ok: Bool) -> Result(Int, Int)\n  if ok then Ok(41) else Err(7)\n\nfn run(ok: Bool) -[Fail Int]> Int\n  step(ok)?\n\nfn main() -> Int\n  let r = catch run(true)\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
            "kea-cli-try-sugar-ok",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 41);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_catch_fails_when_body_cannot_fail() {
        let source_path = write_temp_source(
            "effect Fail\n  fn fail(err: Int) -> Never\n\nfn main() -> Int\n  let r = catch 42\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
            "kea-cli-catch-cannot-fail",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject unnecessary catch");
        assert!(
            err.contains("expression cannot fail; catch is unnecessary"),
            "expected unnecessary catch diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_trait_qualified_method_single_impl_exit_code() {
        let source_path = write_temp_source(
            "trait Inc a\n  fn inc(x: a) -> a\n\nimpl Inc for Int\n  fn inc(x: Int) -> Int\n    x + 1\n\nfn main() -> Int\n  Inc.inc(41)\n",
            "kea-cli-trait-qualified-single-impl",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_trait_qualified_method_ambiguous_impls_error() {
        let source_path = write_temp_source(
            "trait Inc a\n  fn inc(x: a) -> a\n\nimpl Inc for Int\n  fn inc(x: Int) -> Int\n    x + 1\n\nimpl Inc for Float\n  fn inc(x: Float) -> Float\n    x + 1.0\n\nfn main() -> Int\n  Inc.inc(41)\n",
            "kea-cli-trait-qualified-ambiguous-impls",
            "kea",
        );

        let err =
            run_file(&source_path).expect_err("run should reject unresolved trait dispatch target");
        assert!(
            err.contains("unresolved qualified call target `Inc.inc`"),
            "expected unresolved qualified call target diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_bool_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case true\n    true -> 3\n    false -> 8\n",
            "kea-cli-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 3);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_bool_case_var_fallback_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case false\n    true -> 3\n    b -> if b then 8 else 6\n",
            "kea-cli-bool-var-fallback-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_int_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 2\n    1 -> 4\n    2 -> 6\n    _ -> 9\n",
            "kea-cli-int-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_float_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 2.5\n    1.5 -> 4\n    2.5 -> 6\n    _ -> 9\n",
            "kea-cli-float-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_expression_scrutinee_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 1 + 1\n    1 -> 4\n    2 -> 6\n    _ -> 9\n",
            "kea-cli-expr-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_case_var_fallback_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 2\n    1 -> 4\n    n -> n\n",
            "kea-cli-case-var-fallback",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 2);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_unit_enum_case_exit_code() {
        let source_path = write_temp_source(
            "type Color = Red | Green\n\nfn main() -> Int\n  case Color.Red\n    Color.Red -> 1\n    Color.Green -> 2\n",
            "kea-cli-unit-enum-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_int_or_pattern_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 2\n    0 | 1 -> 4\n    2 | 3 -> 7\n    _ -> 9\n",
            "kea-cli-int-or-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_unit_enum_or_pattern_case_exit_code() {
        let source_path = write_temp_source(
            "type Color = Red | Green | Blue\n\nfn main() -> Int\n  case Color.Green\n    Color.Red | Color.Green -> 3\n    _ -> 8\n",
            "kea-cli-unit-enum-or-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 3);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_unqualified_unit_enum_case_exit_code() {
        let source_path = write_temp_source(
            "type Color = Red | Green\n\nfn main() -> Int\n  case Red\n    Red -> 5\n    Green -> 9\n",
            "kea-cli-unit-enum-unqualified-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 5);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_literal_as_pattern_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 0\n    0 as n -> n + 7\n    _ -> 1\n",
            "kea-cli-literal-as-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_literal_case_guard_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 2\n    2 when true -> 6\n    _ -> 9\n",
            "kea-cli-literal-guard-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_literal_as_guard_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 0\n    0 as n when n == 0 -> n + 8\n    _ -> 1\n",
            "kea-cli-literal-as-guard-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 8);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_unit_enum_guard_case_exit_code() {
        let source_path = write_temp_source(
            "type Color = Red | Green\n\nfn main() -> Int\n  case Color.Red\n    Color.Red when true -> 4\n    _ -> 1\n",
            "kea-cli-unit-enum-guard-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 4);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_unit_enum_as_guard_case_exit_code() {
        let source_path = write_temp_source(
            "type Color = Red | Green\n\nfn main() -> Int\n  case Color.Red\n    Color.Red as c when true -> 5\n    _ -> 1\n",
            "kea-cli-unit-enum-as-guard-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 5);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_literal_or_guard_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 1\n    0 | 1 when true -> 6\n    _ -> 1\n",
            "kea-cli-literal-or-guard-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_unit_enum_or_guard_case_exit_code() {
        let source_path = write_temp_source(
            "type Color = Red | Green | Blue\n\nfn main() -> Int\n  case Color.Red\n    Color.Red | Color.Green when true -> 7\n    _ -> 1\n",
            "kea-cli-unit-enum-or-guard-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_guarded_var_fallback_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 1\n    0 -> 4\n    n when n == 1 -> n + 8\n    _ -> 1\n",
            "kea-cli-guarded-var-fallback-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 9);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_guarded_wildcard_fallback_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 1\n    0 -> 4\n    _ when true -> 6\n    _ -> 1\n",
            "kea-cli-guarded-wildcard-fallback-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_or_as_pattern_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case 1\n    0 as n | 1 as n -> n + 5\n    _ -> 1\n",
            "kea-cli-or-as-pattern-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_record_pattern_case_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    User { age: 4, .. } -> 6\n    _ -> 2\n",
            "kea-cli-record-pattern-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_record_pattern_direct_expression_scrutinee_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n\nfn main() -> Int\n  case User { age: 7 }\n    User { age: n } -> n\n",
            "kea-cli-record-pattern-direct-scrutinee",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_record_pattern_renamed_field_binding_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    User { age: years, .. } -> years + 2\n    _ -> 0\n",
            "kea-cli-record-pattern-rename-bind",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_record_pattern_pun_binding_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    User { age, .. } -> age + 3\n    _ -> 0\n",
            "kea-cli-record-pattern-pun-bind",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_record_pattern_guard_binding_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    User { age: years, .. } when years == 4 -> years + 10\n    _ -> 0\n",
            "kea-cli-record-pattern-guard-bind",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 14);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_record_pattern_or_literal_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    User { age: 3, .. } | User { age: 4, .. } -> 6\n    _ -> 2\n",
            "kea-cli-record-pattern-or",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_anon_record_pattern_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let user = #{ age: 4, score: 9 }\n  case user\n    #{ age: 4, .. } -> 6\n    _ -> 2\n",
            "kea-cli-anon-record-pattern-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_anon_record_pattern_direct_expression_scrutinee_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case #{ age: 7 }\n    #{ age: n } -> n\n",
            "kea-cli-anon-record-pattern-direct-scrutinee",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_anon_record_pattern_or_literal_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let user = #{ age: 4, score: 9 }\n  case user\n    #{ age: 3, .. } | #{ age: 4, .. } -> 6\n    _ -> 2\n",
            "kea-cli-anon-record-pattern-or",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_anon_record_literal_field_access_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let user = #{ age: 4, score: 9 }\n  user.age\n",
            "kea-cli-anon-record-field",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 4);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_record_construct_and_field_access_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  user.age + user.score\n",
            "kea-cli-record-init-field",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 13);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_dot_method_dispatch_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n\nfn inc(self: User) -> User\n  User { ..self, age: self.age + 1 }\n\nfn main() -> Int\n  let user = User { age: 41 }\n  user.inc().age\n",
            "kea-cli-dot-method-dispatch",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_dot_method_dispatch_on_field_access_receiver_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n\nrecord Wrap\n  inner: User\n\nfn inc(self: User) -> User\n  User { ..self, age: self.age + 1 }\n\nfn main() -> Int\n  let wrapped = Wrap { inner: User { age: 41 } }\n  wrapped.inner.inc().age\n",
            "kea-cli-dot-method-dispatch-field-receiver",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_row_polymorphic_record_field_access_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n  score: Int\n\nfn get_age(u: { age: Int | r }) -> Int\n  u.age\n\nfn main() -> Int\n  let user = User { age: 41, score: 1 }\n  get_age(user)\n",
            "kea-cli-row-poly-record-field",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 41);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_record_update_with_spread_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  let updated = User { ..user, age: user.age + 3 }\n  updated.age + updated.score\n",
            "kea-cli-record-update",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 16);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_nested_record_update_chain_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  let updated = User { ..(User { ..user, age: user.age + 3 }), score: user.score + 4 }\n  updated.age + updated.score\n",
            "kea-cli-record-update-chain",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 20);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_exit_code() {
        let source_path = write_temp_source(
            "type Flag = Yep(Int) | Nope\n\nfn make_flag() -> Flag\n  Yep(7)\n\nfn main() -> Int\n  let ignored = make_flag()\n  3\n",
            "kea-cli-sum-init",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 3);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_sum_payload_record_type_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n\ntype Wrap = W(User) | N\n\nfn main() -> Int\n  case W(User { age: 7 })\n    W(u) -> u.age + 1\n    N -> 0\n",
            "kea-cli-sum-record-payload",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 8);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_sum_payload_record_pattern_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n\ntype Wrap = W(User) | N\n\nfn main() -> Int\n  case W(User { age: 7 })\n    W(User { age: n }) -> n + 2\n    N -> 0\n",
            "kea-cli-sum-record-payload-pattern",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 9);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_sum_payload_record_alias_type_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n\nalias UserAlias = User\n\ntype Wrap = W(UserAlias) | N\n\nfn main() -> Int\n  case W(User { age: 7 })\n    W(u) -> u.age + 5\n    N -> 0\n",
            "kea-cli-sum-record-payload-alias",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 12);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_expression_arg_exit_code() {
        let source_path = write_temp_source(
            "type Flag = Yep(Int) | Nope\n\nfn main() -> Int\n  case Yep(1 + 6)\n    Yep(n) -> n\n    Nope -> 0\n",
            "kea-cli-sum-init-expr-arg",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_named_payload_constructor_labeled_args_exit_code() {
        let source_path = write_temp_source(
            "type Pair = Pair(left: Int, right: Int)\n\nfn main() -> Int\n  case Pair(right: 1, left: 40)\n    Pair(left: a, right: b) -> a * 100 + b\n",
            "kea-cli-sum-init-labeled-args",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 4001);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_qualified_payload_constructor_case_exit_code() {
        let source_path = write_temp_source(
            "type Flag = Yep(Int) | Nope\n\nfn main() -> Int\n  case Flag.Yep(7)\n    Flag.Yep(n) -> n\n    Flag.Nope -> 0\n",
            "kea-cli-sum-init-qualified",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_case_exit_code() {
        let source_path = write_temp_source(
            "type Flag = Yep(Int) | Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(_) -> 11\n    Nope -> 0\n",
            "kea-cli-sum-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 11);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_builtin_result_constructor_case_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case Err(7)\n    Ok(v) -> v\n    Err(e) -> e\n",
            "kea-cli-builtin-result-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_bound_case_exit_code() {
        let source_path = write_temp_source(
            "type Flag = Yep(Int) | Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(n) -> n + 1\n    Nope -> 0\n",
            "kea-cli-sum-case-bind",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 8);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_as_case_exit_code() {
        let source_path = write_temp_source(
            "type Flag = Yep(Int) | Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(n) as whole -> n + 2\n    Nope -> 0\n",
            "kea-cli-sum-case-as",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 9);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_or_case_exit_code() {
        let source_path = write_temp_source(
            "type Flag = Yep(Int) | Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(n) | Yep(n) -> n + 3\n    Nope -> 0\n",
            "kea-cli-sum-case-or",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 10);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_or_across_variants_exit_code() {
        let source_path = write_temp_source(
            "type Either = Left(Int) | Right(Int) | Nope\n\nfn main() -> Int\n  case Right(7)\n    Left(n) | Right(n) -> n + 4\n    Nope -> 0\n",
            "kea-cli-sum-case-or-variants",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 11);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_multi_bind_case_exit_code() {
        let source_path = write_temp_source(
            "type Pair = Pair(Int, Int) | Nope\n\nfn main() -> Int\n  case Pair(4, 6)\n    Pair(a, b) -> a + b\n    Nope -> 0\n",
            "kea-cli-sum-case-multi-bind",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 10);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_literal_check_case_exit_code() {
        let source_path = write_temp_source(
            "type Flag = Yep(Int) | Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(7) -> 14\n    Nope -> 0\n",
            "kea-cli-sum-case-literal-check",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 14);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_mixed_literal_bind_case_exit_code() {
        let source_path = write_temp_source(
            "type Pair = Pair(Int, Int) | Nope\n\nfn main() -> Int\n  case Pair(1, 6)\n    Pair(1, b) -> b + 1\n    Nope -> 0\n",
            "kea-cli-sum-case-mixed-literal-bind",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_nested_payload_constructor_case_exit_code() {
        let source_path = write_temp_source(
            "type Maybe a = Just(a) | Nothing\n\nfn main() -> Int\n  case Just(Just(7))\n    Just(Just(n)) -> n + 8\n    _ -> 0\n",
            "kea-cli-sum-case-nested-payload",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 15);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_nested_or_payload_constructor_case_exit_code() {
        let source_path = write_temp_source(
            "type Inner = A(Int) | B(Int)\ntype Outer = Wrap(Inner) | End\n\nfn main() -> Int\n  case Wrap(B(7))\n    Wrap(A(n) | B(n)) -> n + 12\n    _ -> 0\n",
            "kea-cli-sum-case-nested-or-payload",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 19);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_as_guard_case_exit_code() {
        let source_path = write_temp_source(
            "type Flag = Yep(Int) | Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(n) as whole when n == 7 -> n + 5\n    Yep(_) -> 1\n    Nope -> 0\n",
            "kea-cli-sum-case-as-guard",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 12);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_payload_constructor_or_guard_across_variants_exit_code() {
        let source_path = write_temp_source(
            "type Either = Left(Int) | Right(Int) | Nope\n\nfn main() -> Int\n  case Right(7)\n    Left(n) | Right(n) when n > 0 -> n + 6\n    Left(_) | Right(_) -> 1\n    Nope -> 0\n",
            "kea-cli-sum-case-or-guard-variants",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 13);

        let _ = std::fs::remove_file(source_path);
    }

    fn write_temp_source(contents: &str, prefix: &str, extension: &str) -> PathBuf {
        let path = temp_artifact_path(prefix, extension);
        std::fs::write(&path, contents).expect("temp source write should succeed");
        path
    }

    fn temp_project_dir(prefix: &str) -> PathBuf {
        let path = temp_artifact_path(prefix, "proj");
        std::fs::create_dir_all(&path).expect("temp project dir should be created");
        path
    }

    fn temp_workspace_project_dir(prefix: &str) -> PathBuf {
        let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("workspace root should exist")
            .to_path_buf();
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("time should move forward")
            .as_nanos()
            .to_string();
        let counter = TEMP_NONCE.fetch_add(1, Ordering::Relaxed);
        let path = workspace_root
            .join("target")
            .join("kea-tests")
            .join(format!("{prefix}-{timestamp}-{counter}"));
        std::fs::create_dir_all(&path).expect("workspace temp project dir should be created");
        path
    }

    fn temp_artifact_path(prefix: &str, extension: &str) -> PathBuf {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("time should move forward")
            .as_nanos()
            .to_string();
        let counter = TEMP_NONCE.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir().join(format!("{prefix}-{timestamp}-{counter}.{extension}"))
    }
}
