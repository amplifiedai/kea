use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command as ProcessCommand;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use kea::{compile_file, emit_diagnostics, run_file, run_test_file};
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
        Command::Test { input } => {
            let result = run_test_file(&input)?;
            if result.cases.is_empty() {
                println!("no tests found in {}", input.display());
                return Ok(());
            }

            let mut passed = 0usize;
            let mut failed = 0usize;
            for case in result.cases {
                if case.passed {
                    passed += 1;
                    println!(
                        "ok   {} ({} run{})",
                        case.name,
                        case.iterations,
                        if case.iterations == 1 { "" } else { "s" }
                    );
                } else {
                    failed += 1;
                    match case.error {
                        Some(err) => println!(
                            "FAIL {} ({} run{}): {}",
                            case.name,
                            case.iterations,
                            if case.iterations == 1 { "" } else { "s" },
                            err
                        ),
                        None => println!(
                            "FAIL {} ({} run{})",
                            case.name,
                            case.iterations,
                            if case.iterations == 1 { "" } else { "s" }
                        ),
                    }
                }
            }

            println!("{passed} passed; {failed} failed");
            if failed > 0 {
                std::process::exit(1);
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
    Test {
        input: PathBuf,
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
        "test" => Ok(Command::Test {
            input: PathBuf::from(&args[2]),
        }),
        _ => Err(usage()),
    }
}

fn usage() -> String {
    "usage:\n  kea run <file.kea>\n  kea build <file.kea> [-o output|output.o]\n  kea test <file.kea>".to_string()
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

    let runtime_source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("runtime")
        .join("kea_aot_runtime.c");
    let temp_runtime_object = std::env::temp_dir().join(format!(
        "kea-build-runtime-{}-{timestamp}-{counter}.o",
        std::process::id()
    ));

    let runtime_status = ProcessCommand::new("cc")
        .arg("-c")
        .arg(&runtime_source)
        .arg("-o")
        .arg(&temp_runtime_object)
        .status()
        .map_err(|err| format!("failed to compile AOT runtime shims: {err}"))?;

    if !runtime_status.success() {
        let _ = fs::remove_file(&temp_object);
        return Err(format!(
            "failed to compile AOT runtime shims from `{}` (exit status: {runtime_status})",
            runtime_source.display()
        ));
    }

    let status = ProcessCommand::new("cc")
        .arg(&temp_object)
        .arg(&temp_runtime_object)
        .arg("-o")
        .arg(output)
        .status()
        .map_err(|err| format!("failed to invoke linker `cc`: {err}"))?;

    let _ = fs::remove_file(&temp_object);
    let _ = fs::remove_file(&temp_runtime_object);

    if !status.success() {
        return Err(format!(
            "linker failed for `{}` (exit status: {status})",
            output.display()
        ));
    }

    Ok(())
}


#[cfg(test)]
mod main_tests;
