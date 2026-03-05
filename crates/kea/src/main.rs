use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs;
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::Command as ProcessCommand;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use kea::{
    DepSpec, PackageCommand, PackageManifest, compile_file, emit_diagnostics, execute_pkg_command,
    find_manifest, run_file, run_test_file, serve_mcp_stdio,
};
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
            let input = resolve_command_input(input)?;
            let result = run_file(&input)?;
            emit_diagnostics(&result.diagnostics);
            if result.exit_code != 0 {
                std::process::exit(result.exit_code);
            }
            Ok(())
        }
        Command::Build { input, output } => {
            let input = resolve_command_input(input)?;
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
            let mut passed = 0usize;
            let mut failed = 0usize;
            let mut observed_cases = 0usize;
            let test_targets = resolve_test_targets(input)?;
            if test_targets.files.is_empty() {
                if let Some(package_dir) = &test_targets.package_dir {
                    println!("no tests found in {}", package_dir.display());
                } else {
                    println!("no tests found");
                }
                return Ok(());
            }

            let multi_file = test_targets.files.len() > 1;
            for file in test_targets.files {
                let result = run_test_file(&file)?;
                if result.cases.is_empty() {
                    continue;
                }
                let file_label = format_test_file_label(&file, test_targets.package_dir.as_deref());
                for case in result.cases {
                    observed_cases += 1;
                    let case_name = if multi_file {
                        format!("{file_label}::{}", case.name)
                    } else {
                        case.name.clone()
                    };
                    if case.passed {
                        passed += 1;
                        println!(
                            "ok   {} ({} run{})",
                            case_name,
                            case.iterations,
                            if case.iterations == 1 { "" } else { "s" }
                        );
                    } else {
                        failed += 1;
                        match case.error {
                            Some(err) => println!(
                                "FAIL {} ({} run{}): {}",
                                case_name,
                                case.iterations,
                                if case.iterations == 1 { "" } else { "s" },
                                err
                            ),
                            None => println!(
                                "FAIL {} ({} run{})",
                                case_name,
                                case.iterations,
                                if case.iterations == 1 { "" } else { "s" }
                            ),
                        }
                    }
                }
            }

            if observed_cases == 0 {
                if let Some(package_dir) = &test_targets.package_dir {
                    println!("no tests found in {}", package_dir.display());
                } else {
                    println!("no tests found");
                }
                return Ok(());
            }
            println!("{passed} passed; {failed} failed");
            if failed > 0 {
                std::process::exit(1);
            }
            Ok(())
        }
        Command::Pkg { command } => {
            let message = execute_pkg_command(command)?;
            println!("{message}");
            Ok(())
        }
        Command::Mcp {
            show_help,
            show_version,
        } => {
            if show_help {
                print_mcp_help();
                return Ok(());
            }
            if show_version {
                println!("{}", env!("CARGO_PKG_VERSION"));
                return Ok(());
            }
            if std::io::stdin().is_terminal() || std::io::stdout().is_terminal() {
                return Err(
                    "kea mcp: refusing interactive TTY mode; start via MCP stdio pipes"
                        .to_string(),
                );
            }
            let runtime = tokio::runtime::Builder::new_multi_thread()
                .enable_all()
                .build()
                .map_err(|err| format!("failed to initialize tokio runtime: {err}"))?;
            runtime
                .block_on(serve_mcp_stdio())
                .map_err(|err| format!("kea mcp: {err}"))?;
            Ok(())
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Command {
    Run {
        input: Option<PathBuf>,
    },
    Build {
        input: Option<PathBuf>,
        output: Option<PathBuf>,
    },
    Test {
        input: Option<PathBuf>,
    },
    Pkg {
        command: PackageCommand,
    },
    Mcp {
        show_help: bool,
        show_version: bool,
    },
}

fn parse_cli(args: &[String]) -> Result<Command, String> {
    if args.len() < 2 {
        return Err(usage());
    }

    match args[1].as_str() {
        "run" => {
            let input = args.get(2).map(PathBuf::from);
            if args.len() > 3 {
                return Err(format!("unexpected arguments for `run`\n{}", usage()));
            }
            Ok(Command::Run { input })
        }
        "build" => {
            let mut input = None;
            let mut output = None;

            let mut idx = 2;
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
                        if unknown.starts_with('-') {
                            return Err(format!("unknown argument `{unknown}`\n{}", usage()));
                        }
                        if input.is_some() {
                            return Err(format!(
                                "multiple input files are not supported (`{unknown}` is extra)\n{}",
                                usage()
                            ));
                        }
                        input = Some(PathBuf::from(unknown));
                        idx += 1;
                    }
                }
            }

            Ok(Command::Build { input, output })
        }
        "test" => {
            let input = args.get(2).map(PathBuf::from);
            if args.len() > 3 {
                return Err(format!("unexpected arguments for `test`\n{}", usage()));
            }
            Ok(Command::Test { input })
        }
        "pkg" => parse_pkg_cli(args),
        "mcp" => parse_mcp_cli(args),
        _ => Err(usage()),
    }
}

fn parse_mcp_cli(args: &[String]) -> Result<Command, String> {
    match args.get(2).map(String::as_str) {
        None => Ok(Command::Mcp {
            show_help: false,
            show_version: false,
        }),
        Some("-h") | Some("--help") => {
            if args.len() > 3 {
                return Err(format!("unexpected arguments for `mcp`\n{}", usage()));
            }
            Ok(Command::Mcp {
                show_help: true,
                show_version: false,
            })
        }
        Some("-V") | Some("--version") => {
            if args.len() > 3 {
                return Err(format!("unexpected arguments for `mcp`\n{}", usage()));
            }
            Ok(Command::Mcp {
                show_help: false,
                show_version: true,
            })
        }
        Some(unknown) => Err(format!("unknown argument `{unknown}` for `mcp`\n{}", usage())),
    }
}

fn parse_pkg_cli(args: &[String]) -> Result<Command, String> {
    if args.len() < 3 {
        return Err(format!("missing pkg subcommand\n{}", usage()));
    }
    match args[2].as_str() {
        "init" => {
            if args.len() != 3 {
                return Err(format!("`kea pkg init` takes no arguments\n{}", usage()));
            }
            Ok(Command::Pkg {
                command: PackageCommand::Init,
            })
        }
        "add" => {
            if args.len() < 5 {
                return Err(
                    "usage: kea pkg add <name> (--git <url> [--tag <tag>|--rev <rev>|--branch <branch>] | --path <path>)"
                        .to_string(),
                );
            }
            let name = args[3].clone();
            let mut git = None;
            let mut path = None;
            let mut tag = None;
            let mut rev = None;
            let mut branch = None;
            let mut idx = 4;
            while idx < args.len() {
                match args[idx].as_str() {
                    "--git" => {
                        if idx + 1 >= args.len() {
                            return Err("missing value for --git".to_string());
                        }
                        git = Some(args[idx + 1].clone());
                        idx += 2;
                    }
                    "--path" => {
                        if idx + 1 >= args.len() {
                            return Err("missing value for --path".to_string());
                        }
                        path = Some(args[idx + 1].clone());
                        idx += 2;
                    }
                    "--tag" => {
                        if idx + 1 >= args.len() {
                            return Err("missing value for --tag".to_string());
                        }
                        tag = Some(args[idx + 1].clone());
                        idx += 2;
                    }
                    "--rev" => {
                        if idx + 1 >= args.len() {
                            return Err("missing value for --rev".to_string());
                        }
                        rev = Some(args[idx + 1].clone());
                        idx += 2;
                    }
                    "--branch" => {
                        if idx + 1 >= args.len() {
                            return Err("missing value for --branch".to_string());
                        }
                        branch = Some(args[idx + 1].clone());
                        idx += 2;
                    }
                    unknown => {
                        return Err(format!("unknown argument `{unknown}`\n{}", usage()));
                    }
                }
            }

            let spec = match (git, path) {
                (Some(url), None) => DepSpec::Git {
                    url,
                    tag,
                    rev,
                    branch,
                },
                (None, Some(path)) => {
                    if tag.is_some() || rev.is_some() || branch.is_some() {
                        return Err(
                            "`--tag`, `--rev`, and `--branch` are only valid with `--git`"
                                .to_string(),
                        );
                    }
                    DepSpec::Path {
                        path: PathBuf::from(path),
                    }
                }
                (Some(_), Some(_)) => {
                    return Err("dependency can use either --git or --path, not both".to_string());
                }
                (None, None) => {
                    return Err("dependency must specify either --git or --path".to_string());
                }
            };

            Ok(Command::Pkg {
                command: PackageCommand::Add { name, spec },
            })
        }
        "update" => {
            if args.len() > 4 {
                return Err(format!(
                    "usage: kea pkg update [dependency-name]\n{}",
                    usage()
                ));
            }
            Ok(Command::Pkg {
                command: PackageCommand::Update {
                    dependency: args.get(3).cloned(),
                },
            })
        }
        unknown => Err(format!("unknown pkg subcommand `{unknown}`\n{}", usage())),
    }
}

fn usage() -> String {
    "usage:\n  kea run [file.kea]\n  kea build [file.kea] [-o output|output.o]\n  kea test [file.kea]\n  kea mcp [--help|--version]\n  kea pkg init\n  kea pkg add <name> (--git <url> [--tag <tag>|--rev <rev>|--branch <branch>] | --path <path>)\n  kea pkg update [dependency-name]".to_string()
}

fn print_mcp_help() {
    println!(
        "\
kea mcp {}

Run the Kea MCP server over stdio transport.
This command must be started by an MCP client with stdin/stdout pipes.

Usage:
  kea mcp
  kea mcp --help
  kea mcp --version
",
        env!("CARGO_PKG_VERSION")
    );
}

fn resolve_command_input(input: Option<PathBuf>) -> Result<PathBuf, String> {
    if let Some(path) = input {
        return Ok(path);
    }
    let cwd = std::env::current_dir().map_err(|err| format!("failed to read cwd: {err}"))?;
    let manifest_path = find_manifest(&cwd).ok_or_else(|| {
        "no input file provided and no `kea.toml` found in current directory or ancestors"
            .to_string()
    })?;
    let manifest = PackageManifest::load(&manifest_path)?;
    Ok(manifest.entry_path())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TestTargets {
    files: Vec<PathBuf>,
    package_dir: Option<PathBuf>,
}

fn resolve_test_targets(input: Option<PathBuf>) -> Result<TestTargets, String> {
    let cwd = std::env::current_dir().map_err(|err| format!("failed to read cwd: {err}"))?;
    resolve_test_targets_from_cwd(input, &cwd)
}

fn resolve_test_targets_from_cwd(input: Option<PathBuf>, cwd: &Path) -> Result<TestTargets, String> {
    if let Some(path) = input {
        return Ok(TestTargets {
            files: vec![path],
            package_dir: None,
        });
    }

    let Some(manifest_path) = find_manifest(cwd) else {
        return Err(
            "no input file provided and no `kea.toml` found in current directory or ancestors"
                .to_string(),
        );
    };
    let manifest = PackageManifest::load(&manifest_path)?;
    let package_dir = manifest.package_dir();
    let files = discover_package_test_files(&package_dir)?;
    Ok(TestTargets {
        files,
        package_dir: Some(package_dir),
    })
}

fn discover_package_test_files(package_dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut files = BTreeSet::new();

    let tests_dir = package_dir.join("tests");
    if tests_dir.is_dir() {
        let mut entries = fs::read_dir(&tests_dir)
            .map_err(|err| format!("failed to list `{}`: {err}", tests_dir.display()))?
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .collect::<Vec<_>>();
        entries.sort();
        for path in entries {
            if path.is_file() && path.extension().and_then(OsStr::to_str) == Some("kea") {
                files.insert(path);
            }
        }
    }

    let src_dir = package_dir.join("src");
    if src_dir.is_dir() {
        discover_src_test_files(&src_dir, &mut files)?;
    }

    Ok(files.into_iter().collect())
}

fn discover_src_test_files(dir: &Path, out: &mut BTreeSet<PathBuf>) -> Result<(), String> {
    let mut entries = fs::read_dir(dir)
        .map_err(|err| format!("failed to list `{}`: {err}", dir.display()))?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            discover_src_test_files(&path, out)?;
            continue;
        }
        if path.extension().and_then(OsStr::to_str) != Some("kea") {
            continue;
        }
        if !path
            .file_stem()
            .and_then(OsStr::to_str)
            .is_some_and(|stem| stem.ends_with("_test"))
        {
            continue;
        }
        out.insert(path);
    }
    Ok(())
}

fn format_test_file_label(file: &Path, package_dir: Option<&Path>) -> String {
    if let Some(package_dir) = package_dir
        && let Ok(relative) = file.strip_prefix(package_dir)
    {
        return relative.display().to_string();
    }
    file.display().to_string()
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
