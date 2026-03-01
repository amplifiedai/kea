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
    fn parse_test_command() {
        let args = vec![
            "kea".to_string(),
            "test".to_string(),
            "suite.kea".to_string(),
        ];
        let command = parse_cli(&args).expect("cli parse should succeed");
        assert_eq!(
            command,
            Command::Test {
                input: PathBuf::from("suite.kea"),
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
    fn run_test_file_reports_pass_and_fail_without_stopping() {
        let source_path = write_temp_source(
            "effect Fail E\n  fn fail(error: E) -> Never\n\nfn assert(value: Bool) -[Fail String]> Unit\n  if value\n    ()\n  else\n    Fail.fail(\"assertion failed\")\n\ntest \"pass\"\n  assert true\n\ntest \"fail\"\n  assert false\n",
            "kea-cli-test-runner",
            "kea",
        );

        let run = run_test_file(&source_path).expect("test run should succeed");
        assert_eq!(run.cases.len(), 2);
        assert!(
            run.cases
                .iter()
                .any(|case| case.name == "pass" && case.passed)
        );
        assert!(
            run.cases
                .iter()
                .any(|case| case.name == "fail" && !case.passed)
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn run_test_file_supports_stdlib_test_assert_module() {
        let project_dir = temp_workspace_project_dir("kea-cli-test-runner-stdlib-assert");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");
        let source_path = src_dir.join("suite.kea");
        std::fs::write(
            &source_path,
            "use Test\n\ntest \"stdlib assert pass\"\n  Test.assert(1 + 1 == 2)\n\ntest \"stdlib assert fail\"\n  Test.assert(false)\n",
        )
        .expect("suite write should succeed");

        let run = run_test_file(&source_path).expect("test run should succeed");
        assert_eq!(run.cases.len(), 2);
        assert!(
            run.cases
                .iter()
                .any(|case| case.name == "stdlib assert pass" && case.passed)
        );
        assert!(
            run.cases
                .iter()
                .any(|case| case.name == "stdlib assert fail" && !case.passed)
        );

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn run_test_file_executes_property_iterations() {
        let source_path = write_temp_source(
            "effect Fail E\n  fn fail(error: E) -> Never\n\nfn assert(value: Bool) -[Fail String]> Unit\n  if value\n    ()\n  else\n    Fail.fail(\"assertion failed\")\n\ntest property (iterations: 3) \"repeat pass\"\n  assert true\n",
            "kea-cli-test-runner-property-iterations",
            "kea",
        );

        let run = run_test_file(&source_path).expect("test run should succeed");
        assert_eq!(run.cases.len(), 1);
        assert_eq!(run.cases[0].name, "repeat pass");
        assert_eq!(run.cases[0].iterations, 3);
        assert!(run.cases[0].passed);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn run_stdlib_case_corpus_with_kea_test_runner() {
        let cases_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/stdlib_cases");
        let supported = [
            "clock_tests.kea",
            "eq_tests.kea",
            "float_tests.kea",
            "int_tests.kea",
            "io_tests.kea",
            "list_tests.kea",
            "net_tests.kea",
            "option_tests.kea",
            "ord_tests.kea",
            "order_tests.kea",
            "prelude_tests.kea",
            "rand_tests.kea",
            "result_tests.kea",
            "show_tests.kea",
            "test_tests.kea",
            "text_tests.kea",
        ];
        let mut case_files = std::fs::read_dir(&cases_dir)
            .expect("stdlib case dir should exist")
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| supported.contains(&name))
            })
            .collect::<Vec<_>>();
        case_files.sort();
        assert!(
            case_files.len() == supported.len(),
            "expected {} supported stdlib case files in {}",
            supported.len(),
            cases_dir.display()
        );

        let mut failures = Vec::new();
        for case_file in &case_files {
            match run_test_file(case_file) {
                Ok(run) => {
                    if run.cases.is_empty() {
                        failures.push(format!(
                            "{}: no test declarations executed",
                            case_file.display()
                        ));
                        continue;
                    }
                    for case in run.cases {
                        if !case.passed {
                            failures.push(format!(
                                "{}: {} ({})",
                                case_file.display(),
                                case.name,
                                case.error.unwrap_or_else(|| "unknown failure".to_string())
                            ));
                        }
                    }
                }
                Err(err) => failures.push(format!("{}: {err}", case_file.display())),
            }
        }

        assert!(
            failures.is_empty(),
            "stdlib case corpus failures:\n{}",
            failures.join("\n")
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
    fn compile_and_execute_struct_const_field_exit_code() {
        let source_path = write_temp_source(
            "struct Math\n  const pi: Int = 41\n\nfn main() -> Int\n  Math.pi + 1\n",
            "kea-cli-const-field",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_struct_const_field_dependency_exit_code() {
        let source_path = write_temp_source(
            "struct Math\n  const pi: Int = 21\n  const tau: Int = pi * 2\n\nfn main() -> Int\n  Math.tau\n",
            "kea-cli-const-field-deps",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_struct_const_field_rejects_function_calls() {
        let source_path = write_temp_source(
            "fn inc(x: Int) -> Int\n  x + 1\n\nstruct Math\n  const bad: Int = inc(1)\n\nfn main() -> Int\n  Math.bad\n",
            "kea-cli-const-field-call-reject",
            "kea",
        );

        let err = run_file(&source_path).expect_err("const initializer calls should be rejected");
        assert!(
            err.contains("const initializer")
                && err.contains("not supported yet"),
            "expected const initializer rejection, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_struct_const_field_rejects_circular_reference() {
        let source_path = write_temp_source(
            "struct Loop\n  const a: Int = b + 1\n  const b: Int = a + 1\n\nfn main() -> Int\n  Loop.a\n",
            "kea-cli-const-field-cycle-reject",
            "kea",
        );

        let err = run_file(&source_path).expect_err("circular const dependency should be rejected");
        assert!(
            err.contains("circular const dependency"),
            "expected cycle error, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_case_on_struct_const_pattern_exit_code() {
        let source_path = write_temp_source(
            "struct Math\n  const answer: Int = 42\n\nfn classify(x: Int) -> Int\n  case x\n    Math.answer -> 1\n    _ -> 0\n\nfn main() -> Int\n  classify(42)\n",
            "kea-cli-const-field-pattern",
            "kea",
        );

        let run = run_file(&source_path).expect("const pattern case should run");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_case_on_struct_const_pattern_requires_fallback() {
        let source_path = write_temp_source(
            "struct Math\n  const answer: Int = 42\n\nfn classify(x: Int) -> Int\n  case x\n    Math.answer -> 1\n\nfn main() -> Int\n  classify(0)\n",
            "kea-cli-const-field-pattern-non-exhaustive",
            "kea",
        );

        let err = run_file(&source_path).expect_err("const-only case should be non-exhaustive");
        assert!(
            err.contains("non-exhaustive"),
            "expected non-exhaustive diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
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
    fn compile_and_execute_real_stdlib_io_helpers_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-io-helpers");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use IO\n\nfn main() -[IO]> Int\n  IO.print(\"a\")\n  IO.println(\"b\")\n  IO.eprint(\"c\")\n  IO.eprintln(\"d\")\n  1\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_real_stdlib_io_read_write_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-io-read-write");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");
        let io_file_path = project_dir.join("runtime-io.txt");
        let io_missing_path = project_dir.join("runtime-io-missing.txt");
        let io_file_literal = io_file_path.to_string_lossy().replace('\\', "\\\\");
        let io_missing_literal = io_missing_path.to_string_lossy().replace('\\', "\\\\");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            format!(
                "use IO\n\nfn main() -[IO]> Int\n  IO.write_file(\"{io_file_literal}\", \"hello\")\n  let msg = IO.read_file(\"{io_file_literal}\")\n  let missing = IO.read_file(\"{io_missing_literal}\")\n  if msg != missing\n    1\n  else\n    0\n"
            ),
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(io_file_path);
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
    fn compile_and_execute_real_stdlib_clock_helpers_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-clock-helpers");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Clock\n\nfn main() -[Clock]> Int\n  let start = Clock.monotonic()\n  if Clock.elapsed_since(start) >= 0\n    1\n  else\n    0\n",
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
    fn compile_and_execute_real_stdlib_rand_helpers_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-rand-helpers");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Rand\n\nfn main() -[Rand]> Int\n  Rand.seed(123)\n  let n = Rand.int_between(10, 20)\n  if n >= 10 and n <= 20\n    1\n  else\n    0\n",
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
        let listener =
            std::net::TcpListener::bind("127.0.0.1:0").expect("listener bind should succeed");
        let addr = listener.local_addr().expect("listener addr should resolve");
        let server = std::thread::spawn(move || {
            use std::io::{Read, Write};
            if let Ok((mut stream, _)) = listener.accept() {
                let mut buffer = [0u8; 16];
                let read = stream.read(&mut buffer).unwrap_or(0);
                let _ = stream.write_all(&buffer[..read.min(4)]);
            }
        });

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            format!(
                "use Net\n\nfn main() -[Net]> Int\n  let c = Net.connect(\"{addr}\")\n  Net.send(c, \"ping\")\n  let n = Net.recv(c, 4)\n  if c >= 0 and n == 4\n    1\n  else\n    0\n"
            ),
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);
        server.join().expect("net echo server should exit cleanly");

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_real_stdlib_net_helpers_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-net-helpers");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");
        let listener =
            std::net::TcpListener::bind("127.0.0.1:0").expect("listener bind should succeed");
        let addr = listener.local_addr().expect("listener addr should resolve");
        let server = std::thread::spawn(move || {
            use std::io::{Read, Write};
            if let Ok((mut stream, _)) = listener.accept() {
                let mut buffer = [0u8; 16];
                let read = stream.read(&mut buffer).unwrap_or(0);
                let _ = stream.write_all(&buffer[..read.min(4)]);
            }
        });

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            format!(
                "use Net\n\nfn main() -[Net]> Int\n  let c = Net.connect(\"{addr}\")\n  let n = Net.send_and_recv(c, \"ping\", 4)\n  if c >= 0 and n == 4\n    1\n  else\n    0\n"
            ),
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);
        server.join().expect("net echo server should exit cleanly");

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
        let io_file_path = std::env::temp_dir().join(format!(
            "kea-cli-io-read-write-direct-{}.txt",
            std::process::id()
        ));
        let io_missing_path = std::env::temp_dir().join(format!(
            "kea-cli-io-read-write-direct-missing-{}.txt",
            std::process::id()
        ));
        let io_file_literal = io_file_path.to_string_lossy().replace('\\', "\\\\");
        let io_missing_literal = io_missing_path.to_string_lossy().replace('\\', "\\\\");
        let source_path = write_temp_source(
            &format!(
                "effect IO\n  fn write_file(path: String, data: String) -> Unit\n  fn read_file(path: String) -> String\n\nfn main() -[IO]> Int\n  IO.write_file(\"{io_file_literal}\", \"hello\")\n  let msg = IO.read_file(\"{io_file_literal}\")\n  let missing = IO.read_file(\"{io_missing_literal}\")\n  if msg != missing\n    1\n  else\n    0\n"
            ),
            "kea-cli-io-read-write-direct",
            "kea",
        );

        let run = run_file(&source_path).expect("io-read-write run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
        let _ = std::fs::remove_file(io_file_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_and_execute_net_direct_effect_exit_code() {
        let listener =
            std::net::TcpListener::bind("127.0.0.1:0").expect("listener bind should succeed");
        let addr = listener.local_addr().expect("listener addr should resolve");
        let server = std::thread::spawn(move || {
            use std::io::{Read, Write};
            if let Ok((mut stream, _)) = listener.accept() {
                let mut buffer = [0u8; 16];
                let read = stream.read(&mut buffer).unwrap_or(0);
                let _ = stream.write_all(&buffer[..read.min(4)]);
            }
        });
        let source_path = write_temp_source(
            &format!(
                "effect Net\n  fn connect(addr: String) -> Int\n  fn send(conn: Int, data: String) -> Unit\n  fn recv(conn: Int, size: Int) -> Int\n\nfn main() -[Net]> Int\n  let c = Net.connect(\"{addr}\")\n  Net.send(c, \"ping\")\n  let n = Net.recv(c, 4)\n  if c >= 0 and n == 4\n    1\n  else\n    0\n"
            ),
            "kea-cli-net-direct",
            "kea",
        );

        let run = run_file(&source_path).expect("net-direct run should succeed");
        assert_eq!(run.exit_code, 1);
        server.join().expect("net echo server should exit cleanly");

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
            "trait Tinc a\n  fn tinc(x: a) -> a\n\nInt as Tinc\n  fn tinc(x: Int) -> Int\n    x + 1\n",
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
            "use Option\nuse Text\n\nfn main() -> Int\n  Option.unwrap_or(Some(39), 0) + Text.length(\"abc\")\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_option_payload_case_on_function_param_exit_code() {
        let source_path = write_temp_source(
            "fn unwrap_or(opt: Option Int, fallback: Int) -> Int\n  case opt\n    Some(value) -> value\n    None -> fallback\n\nfn main() -> Int\n  unwrap_or(Some(7), 0)\n",
            "kea-cli-option-param-payload-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
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
    fn compile_and_execute_real_stdlib_list_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-list");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use List\n\nfn inc(x: Int) -> Int\n  x + 1\n\nfn even(x: Int) -> Bool\n  x % 2 == 0\n\nfn add(acc: Int, x: Int) -> Int\n  acc + x\n\nfn main() -> Int\n  let xs = Cons(1, Cons(2, Cons(3, Cons(4, Nil))))\n  let ys = List.map(xs, inc)\n  let zs = List.filter(ys, even)\n  if List.is_empty(Nil) and List.length(zs) == 2\n    List.fold(zs, 0, add)\n  else\n    0\n",
        )
            .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_generic_list_enum_exit_code() {
        let project_dir = temp_project_dir("kea-cli-generic-list-enum");
        let src_dir = project_dir.join("src");
        let stdlib_dir = project_dir.join("stdlib");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");
        std::fs::create_dir_all(&stdlib_dir).expect("stdlib dir should be created");
        std::fs::write(stdlib_dir.join("prelude.kea"), "fn ping() -> Int\n  7\n")
            .expect("prelude module write should succeed");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "enum List a\n  Nil\n  Cons(a, List a)\n\nfn length(xs: List Int) -> Int\n  case xs\n    Nil -> 0\n    Cons(_, rest) -> 1 + length(rest)\n\nfn main() -> Int\n  length(Cons(1, Cons(2, Cons(3, Nil))))\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 3);

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
    fn compile_and_execute_real_stdlib_state_effect_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-state");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use State\n\nfn run() -[State Int]> Int\n  State.put(5)\n  State.get()\n\nfn main() -> Int\n  handle run()\n    State.get() -> resume 0\n    State.put(next) -> resume ()\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 5);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_state_with_state_helper_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-state-with-state");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use State\n\nfn bump() -[State Int]> Int\n  let s = State.get()\n  State.put(s + 1)\n  State.get()\n\nfn main() -> Int\n  let pair = State.with_state(41, bump)\n  pair.0 + pair.1\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 84);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_log_effect_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-log");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Log\n\nfn emit() -[Log]> Int\n  Log.debug(\"d\")\n  Log.info(\"i\")\n  Log.warn(\"w\")\n  Log.error(\"e\")\n  7\n\nfn main() -> Int\n  handle emit()\n    Log.debug(msg) -> resume ()\n    Log.info(msg) -> resume ()\n    Log.warn(msg) -> resume ()\n    Log.error(msg) -> resume ()\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_log_with_collected_logs_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-log-collected");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Log\nuse List\n\nfn run() -[Log]> Int\n  Log.debug(\"d\")\n  Log.error(\"e\")\n  7\n\nfn main() -> Int\n  let pair = Log.with_collected_logs(run)\n  let value = pair.0\n  let logs = pair.1\n  if value == 7 and List.length(logs) == 2\n    42\n  else\n    0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_reader_effect_module_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-reader");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Reader\n\nfn main() -> Int\n  handle Reader.ask()\n    Reader.ask() -> resume 41\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 41);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_real_stdlib_reader_helpers_exit_code() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-real-stdlib-reader-helpers");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Reader\n\nfn main() -> Int\n  Reader.with_reader(41, || Reader.asks(|x| x + 1))\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_trait_method_return_type_from_imported_module_exit_code() {
        let project_dir =
            temp_workspace_project_dir("kea-cli-project-trait-method-return-imported-module");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Order\n\ntrait Ord a\n  fn compare(a: a, b: a) -> Ordering\n\nfn main() -> Int\n  0\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("run should succeed");
        assert_eq!(run.exit_code, 0);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_prelude_reexports_module_qualified_helpers_without_collisions() {
        let project_dir = temp_workspace_project_dir("kea-cli-project-prelude-module-reexports");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "fn inc(x: Int) -> Int\n  x + 1\n\nfn main() -> Int\n  let _ = Option.map(Some(1), inc)\n  let _ = Result.from_option(Some(2), 0)\n  let _ = Result.unwrap_or(Err(9), 4)\n  let _ = List.map(List.Cons(3, List.Nil), inc)\n  let _ = Show.show(5)\n  0\n",
        )
        .expect("app module write should succeed");

        let _compiled = compile_file(&app_path, CodegenMode::Aot).expect("compile should succeed");

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
            "enum Ordering\n  Less\n  Equal\n  Greater\n",
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
            "enum List\n  Empty\n  Item(Int)\n\nfn size(_ self: List) -> Int\n  1\n",
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
            "enum List\n  Empty\n  Item(Int)\n\nfn size(xs: List) -> Int\n  case xs\n    Empty -> 0\n    Item(n) -> n + 8\n",
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
        _call_form: MatrixCallForm,
        _import_state: MatrixImportState,
        relation: MatrixModuleRelation,
    ) -> bool {
        if matches!(relation, MatrixModuleRelation::SameModule) {
            return true;
        }
        true
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
                    std::fs::write(stdlib_dir.join("prelude.kea"), "fn ping() -> Int\n  7\n")
                        .expect("prelude write should succeed");

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
                        let err = match run {
                            Ok(run) => panic!(
                                "expected resolution failure for relation={relation:?}, import={import_state:?}, call={call_form:?}, got run result: {run:?}"
                            ),
                            Err(err) => err,
                        };
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
                                "trait Tinc a\n  fn tinc(x: a) -> a\n\nInt as Tinc\n  fn tinc(x: Int) -> Int\n    x + 1"
                                    .to_string(),
                            );
                        }
                        MatrixModuleRelation::CrossModule => match import_state {
                            MatrixImportState::Prelude => {
                                std::fs::write(
                                    stdlib_dir.join("prelude.kea"),
                                    "trait Tinc a\n  fn tinc(x: a) -> a\n\nInt as Tinc\n  fn tinc(x: Int) -> Int\n    x + 1\n",
                                )
                                .expect("prelude write should succeed");
                            }
                            MatrixImportState::NotImported => {
                                std::fs::write(
                                    src_dir.join("tinc.kea"),
                                    "trait Tinc a\n  fn tinc(x: a) -> a\n\nInt as Tinc\n  fn tinc(x: Int) -> Int\n    x + 1\n",
                                )
                                .expect("tinc write should succeed");
                            }
                            MatrixImportState::UseModule => {
                                std::fs::write(
                                    src_dir.join("tinc.kea"),
                                    "trait Tinc a\n  fn tinc(x: a) -> a\n\nInt as Tinc\n  fn tinc(x: Int) -> Int\n    x + 1\n",
                                )
                                .expect("tinc write should succeed");
                                imports.push("use Tinc".to_string());
                            }
                            MatrixImportState::UseModuleNamed => {
                                std::fs::write(
                                    src_dir.join("tinc.kea"),
                                    "trait Tinc a\n  fn tinc(x: a) -> a\n\nInt as Tinc\n  fn tinc(x: Int) -> Int\n    x + 1\n",
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
                        let err = match run {
                            Ok(run) => panic!(
                                "expected resolution failure for relation={relation:?}, import={import_state:?}, call={call_form:?}, got run result: {run:?}"
                            ),
                            Err(err) => err,
                        };
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
                    let list_module_source = "enum List\n  Empty\n  Item(Int)\n\nfn size(xs: List) -> Int\n  case xs\n    Empty -> 0\n    Item(n) -> n + 8\n";
                    let app_module_source = "enum App\n  Empty\n  Item(Int)\n\nfn size(xs: App) -> Int\n  case xs\n    Empty -> 0\n    Item(n) -> n + 8\n";
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
                        let err = match run {
                            Ok(run) => panic!(
                                "expected resolution failure for relation={relation:?}, import={import_state:?}, call={call_form:?}, got run result: {run:?}"
                            ),
                            Err(err) => err,
                        };
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
    fn compile_and_execute_string_interpolation_exit_code() {
        let source_path = write_temp_source(
            "use Text\n\nfn main() -> Int\n  let x = 42\n  if Text.length(\"x is {x}\") == 7\n    1\n  else\n    0\n",
            "kea-cli-string-interp-int",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_string_interpolation_with_escaped_braces_exit_code() {
        let source_path = write_temp_source(
            "use Text\n\nfn main() -> Int\n  let n = 7\n  if Text.length(\"n={n}, literal: {{ok}}\") == 18\n    1\n  else\n    0\n",
            "kea-cli-string-interp-escaped-braces",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_program_with_crlf_line_endings_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\r\n  7\r\n",
            "kea-cli-crlf-line-endings",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed with CRLF line endings");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_tabs_in_indentation() {
        let source_path = write_temp_source(
            "fn main() -> Int\n\t7\n",
            "kea-cli-tabs-in-indentation",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject tabs in indentation");
        assert!(
            err.contains("tabs are not allowed in indentation"),
            "expected tab-indentation diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_keyword_as_binding_name() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let if = 1\n  if\n",
            "kea-cli-keyword-binding-name",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject keyword binding names");
        assert!(
            err.contains("expected pattern"),
            "expected keyword-as-binding parse diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_pipe_operator_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  x |> f\n",
            "kea-cli-reject-pipe-operator",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject pipe syntax");
        assert!(
            err.contains("expected pattern"),
            "expected no-pipe diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_coloncolon_namespace_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  List::length([])\n",
            "kea-cli-reject-coloncolon",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject `::` namespace syntax");
        assert!(
            err.contains("expected expression"),
            "expected no-coloncolon diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_double_ampersand_operator_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  if true && false\n    1\n  else\n    0\n",
            "kea-cli-reject-double-ampersand",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject && operator syntax");
        assert!(
            err.contains("operator '&&' is not supported; use 'and' instead"),
            "expected && rejection diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_bang_prefix_boolean_operator_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  if !true\n    1\n  else\n    0\n",
            "kea-cli-reject-bang-not",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject ! operator syntax");
        assert!(
            err.contains("unexpected character '!'; use 'not' instead"),
            "expected ! rejection diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_nil_literal_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let x = nil\n  0\n",
            "kea-cli-reject-nil-literal",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject nil literal syntax");
        assert!(
            err.contains("`nil` is not supported; use `None`"),
            "expected nil rejection diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_bare_lambda_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let f = x -> x + 1\n  f(1)\n",
            "kea-cli-reject-bare-lambda",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject bare lambda syntax");
        assert!(
            err.contains("bare lambda syntax is not supported; use `|x| expr`"),
            "expected bare-lambda rejection diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_parenthesized_lambda_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let f = (x) -> x + 1\n  f(1)\n",
            "kea-cli-reject-parenthesized-lambda",
            "kea",
        );

        let err =
            run_file(&source_path).expect_err("run should reject parenthesized lambda syntax");
        assert!(
            err.contains("parenthesized lambda syntax is not supported; use `|x| expr`"),
            "expected parenthesized-lambda rejection diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_legacy_derive_attribute_syntax() {
        let source_path = write_temp_source(
            "#[derive(Eq)]\nstruct Point\n  x: Int\n\nfn main() -> Int\n  0\n",
            "kea-cli-reject-legacy-derive",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject legacy derive syntax");
        assert!(
            err.contains("legacy `#[derive(...)]` is not supported; use postfix `deriving Eq, Display`"),
            "expected legacy derive diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_frame_literal_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let _x = frame { x: [1, 2, 3] }\n  0\n",
            "kea-cli-reject-frame-literal",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject frame literals");
        assert!(
            err.contains("`frame` literals are not supported in Kea v0"),
            "expected frame-literal diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_sql_block_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let _x = sql { SELECT 1 AS x }\n  0\n",
            "kea-cli-reject-sql-block",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject sql blocks");
        assert!(
            err.contains("`sql { ... }` blocks are not supported in Kea v0"),
            "expected sql-block diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_html_block_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let _x = html { <h1>${:name}</h1> }\n  0\n",
            "kea-cli-reject-html-block",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject html blocks");
        assert!(
            err.contains("`html { ... }` blocks are not supported in Kea v0"),
            "expected html-block diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_markdown_block_syntax() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let _x = markdown { # ${:title}\\n\\nCount: ${1} }\n  0\n",
            "kea-cli-reject-markdown-block",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject markdown blocks");
        assert!(
            err.contains("`markdown { ... }` blocks are not supported in Kea v0"),
            "expected markdown-block diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_string_interpolation_when_show_is_missing() {
        let source_path = write_temp_source(
            "struct Foo\n  x: Int\n\nfn main() -> Int\n  let f = Foo { x: 1 }\n  if \"{f}\" == \"\"\n    1\n  else\n    0\n",
            "kea-cli-string-interp-missing-show",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject unsupported interpolation");
        assert!(
            err.contains("does not implement trait `Show`"),
            "expected interpolation Show trait-bound error, got: {err}"
        );
        assert!(
            !err.contains("type mismatch"),
            "interpolation errors should surface trait obligations, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_string_interpolation_when_expression_is_empty() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let x = \"{}\"\n  if x == \"\"\n    1\n  else\n    0\n",
            "kea-cli-string-interp-empty-expr",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject empty interpolation");
        assert!(
            err.contains("expected expression in string interpolation"),
            "expected empty interpolation diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_unterminated_string_interpolation() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let x = 1\n  if \"value={x\" == \"\"\n    1\n  else\n    0\n",
            "kea-cli-string-interp-unterminated",
            "kea",
        );

        let err =
            run_file(&source_path).expect_err("run should reject unterminated interpolation");
        assert!(
            err.contains("unterminated interpolation in string"),
            "expected unterminated interpolation diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_unexpected_eof_mid_expression() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  1 +\n",
            "kea-cli-unexpected-eof-mid-expr",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject unexpected EOF");
        assert!(
            err.contains("expected expression"),
            "expected unexpected-EOF diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_reports_multiple_syntax_errors_in_single_function_body() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let x =\n  let y =\n  x + y\n",
            "kea-cli-multiple-syntax-errors",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject malformed function body");
        let surfaced_error_count = err.match_indices("- error[").count();
        assert!(
            surfaced_error_count >= 2,
            "expected at least two surfaced diagnostics, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_resume_outside_handler_clause() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  resume 1\n",
            "kea-cli-resume-outside-handler",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject resume outside handler");
        assert!(
            err.contains("`resume` is only valid inside a matching handler clause"),
            "expected resume-outside diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_handler_clause_that_resumes_multiple_times() {
        let source_path = write_temp_source(
            "effect Ping\n  fn ask() -> Int\n\nfn run() -[Ping]> Int\n  Ping.ask()\n\nfn main() -> Int\n  handle run()\n    Ping.ask() ->\n      if true\n        resume 1\n      else\n        resume 2\n",
            "kea-cli-resume-multiple-times",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject multiple resumes");
        assert!(
            err.contains("handler clause may resume at most once"),
            "expected at-most-once resume diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_resume_captured_by_lambda() {
        let source_path = write_temp_source(
            "effect Ping\n  fn ask() -> Int\n\nfn run() -[Ping]> Int\n  Ping.ask()\n\nfn main() -> Int\n  handle run()\n    Ping.ask() ->\n      let k = |x| resume x\n      k(1)\n",
            "kea-cli-resume-captured-lambda",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject lambda-captured resume");
        assert!(
            err.contains("`resume` cannot be captured in a lambda"),
            "expected lambda-captured resume diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_resume_inside_loop_in_handler_clause() {
        let source_path = write_temp_source(
            "effect Ping\n  fn ask() -> Int\n\nfn run() -[Ping]> Int\n  Ping.ask()\n\nfn main() -> Int\n  handle run()\n    Ping.ask() ->\n      for x in [1]\n        resume x\n",
            "kea-cli-resume-inside-loop",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject resume inside loops");
        assert!(
            err.contains("`resume` is not allowed inside loops in handler clauses"),
            "expected resume-in-loop diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_resume_value_type_mismatch_in_handler_clause() {
        let source_path = write_temp_source(
            "effect Counter\n  fn next() -> Int\n\nfn run() -[Counter]> Int\n  Counter.next()\n\nfn main() -> Int\n  handle run()\n    Counter.next() -> resume \"bad\"\n",
            "kea-cli-resume-type-mismatch",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject resume type mismatch");
        assert!(
            err.contains("type mismatch") && err.contains("Int") && err.contains("String"),
            "expected resume type-mismatch diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_effect_operation_call_with_too_many_arguments() {
        let source_path = write_temp_source(
            "effect Counter\n  fn next() -> Int\n\nfn main() -[Counter]> Int\n  Counter.next(1)\n",
            "kea-cli-effect-op-extra-arg",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject extra call arguments");
        assert!(
            err.contains("too many arguments: expected 0, got 1"),
            "expected operation arity diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_handle_without_operation_clauses() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  handle 1\n    then value -> value\n",
            "kea-cli-handle-empty-clauses",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject empty handle clause set");
        assert!(
            err.contains("handle expression requires at least one operation clause"),
            "expected empty-handle diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_mismatched_handler_target_is_noop_exit_code() {
        let source_path = write_temp_source(
            "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\neffect Log\n  fn log(msg: Int) -> Unit\n\nfn body() -[Log]> Int\n  Log.log(7)\n  42\n\nfn wrap() -[Log]> Int\n  handle body()\n    State.get() -> resume 0\n    State.put(next) -> resume ()\n\nfn main() -> Int\n  handle wrap()\n    Log.log(msg) -> resume ()\n",
            "kea-cli-mismatched-handler-noop",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_with_binding_and_stacking_exit_code() {
        let source_path = write_temp_source(
            "fn with_value(value: Int, @with f: fn(Int) -> Int) -> Int\n  f(value)\n\nfn with_unit(@with f: fn() -> Int) -> Int\n  f()\n\nfn main() -> Int\n  with n <- with_value(40)\n  with with_unit\n  n + 2\n",
            "kea-cli-with-binding-stacking",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_with_after_let_exit_code() {
        let source_path = write_temp_source(
            "fn with_value(value: Int, @with f: fn(Int) -> Int) -> Int\n  f(value)\n\nfn main() -> Int\n  let seed = 41\n  with n <- with_value(seed)\n  n + 1\n",
            "kea-cli-with-after-let",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_with_when_target_is_not_marked_annotation() {
        let source_path = write_temp_source(
            "fn plain(f: fn() -> Int) -> Int\n  f()\n\nfn main() -> Int\n  with plain\n  0\n",
            "kea-cli-with-missing-annotation",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject unannotated with target");
        assert!(
            err.contains("not marked `@with`"),
            "expected @with validation diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_with_on_non_call_expression() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  with 42\n  0\n",
            "kea-cli-with-non-call",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject non-call with head");
        assert!(
            err.contains("expected a direct named function call"),
            "expected with-target shape diagnostic, got: {err}"
        );

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
            "enum Flag\n  Yep(Int)\n  Nope\n\nfn main() -> Int\n  case Yep(1 + 6)\n    Yep(n) -> n\n    Nope -> 0\n",
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
    fn compile_build_and_execute_aot_mutually_recursive_struct_enum_exit_code() {
        let source_path = write_temp_source(
            "struct MatchArm\n  body: HirExpr\n  tag: Int\n\nenum HirExpr\n  Lit(Int)\n  Match(HirExpr, MatchArm)\n\nfn depth(e: HirExpr) -> Int\n  case e\n    Lit(_) -> 0\n    Match(inner, _) -> 1 + depth(inner)\n\nfn main() -> Int\n  let arm = MatchArm { body: Lit(1), tag: 0 }\n  depth(Match(Lit(5), arm))\n",
            "kea-cli-aot-mutual-recursive-type-defs",
            "kea",
        );
        let output_path = temp_artifact_path("kea-cli-aot-mutual-recursive-type-defs", "bin");

        let compiled = compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
        link_object_bytes(&compiled.object, &output_path).expect("link should work");

        let status = std::process::Command::new(&output_path)
            .status()
            .expect("aot executable should run");
        assert_eq!(status.code(), Some(1));

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
    fn compile_build_and_execute_aot_io_read_write_file_exit_code() {
        let io_file_path = std::env::temp_dir().join(format!(
            "kea-cli-aot-io-read-write-{}.txt",
            std::process::id()
        ));
        let io_missing_path = std::env::temp_dir().join(format!(
            "kea-cli-aot-io-read-write-missing-{}.txt",
            std::process::id()
        ));
        let io_file_literal = io_file_path.to_string_lossy().replace('\\', "\\\\");
        let io_missing_literal = io_missing_path.to_string_lossy().replace('\\', "\\\\");
        let source_path = write_temp_source(
            &format!(
                "effect IO\n  fn write_file(path: String, data: String) -> Unit\n  fn read_file(path: String) -> String\n\nfn main() -[IO]> Int\n  IO.write_file(\"{io_file_literal}\", \"hello-aot\")\n  let msg = IO.read_file(\"{io_file_literal}\")\n  let missing = IO.read_file(\"{io_missing_literal}\")\n  if msg != missing\n    1\n  else\n    0\n"
            ),
            "kea-cli-aot-io-read-write",
            "kea",
        );
        let output_path = temp_artifact_path("kea-cli-aot-io-read-write", "bin");

        let compiled =
            compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
        link_object_bytes(&compiled.object, &output_path).expect("link should work");

        let status = std::process::Command::new(&output_path)
            .status()
            .expect("aot executable should run");
        assert_eq!(status.code(), Some(1));

        let _ = std::fs::remove_file(source_path);
        let _ = std::fs::remove_file(output_path);
        let _ = std::fs::remove_file(io_file_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_jit_and_aot_exit_code_parity_corpus() {
        let cases = [
            ("fn main() -> Int\n  let x = 40\n  x + 2\n", 42),
            (
                "struct User\n  age: Int\n\nfn main() -> Int\n  let u = User { age: 41 }\n  u.age + 1\n",
                42,
            ),
            (
                "enum Maybe a\n  Just(a)\n  Nothing\n\nfn main() -> Int\n  case Just(41)\n    Just(n) -> n + 1\n    Nothing -> 0\n",
                42,
            ),
            (
                "fn apply(f: fn(Int) -> Int, x: Int) -> Int\n  f(x)\n\nfn main() -> Int\n  apply(|x| x + 1, 41)\n",
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
    fn compile_and_execute_prefixed_integer_literals_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  0x2A + 0b1010 + 0o10\n",
            "kea-cli-prefixed-int-literals",
            "kea",
        );

        let run = run_file(&source_path).expect("prefixed integer literal run should succeed");
        assert_eq!(run.exit_code, 60);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_underscored_numeric_literals_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  1_000_000 + 0x10\n",
            "kea-cli-underscored-numeric-literals",
            "kea",
        );

        let run = run_file(&source_path).expect("underscored numeric literal run should succeed");
        assert_eq!(run.exit_code, 1_000_016);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_mixed_width_signed_arithmetic_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let a: Int8 = 12\n  let b: Int16 = 30\n  a + b\n",
            "kea-cli-mixed-width-signed-arithmetic",
            "kea",
        );

        let run = run_file(&source_path).expect("mixed-width signed arithmetic should run");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_mixed_width_unsigned_arithmetic_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let a: UInt8 = 10\n  let b: UInt16 = 7\n  a + b\n",
            "kea-cli-mixed-width-unsigned-arithmetic",
            "kea",
        );

        let run = run_file(&source_path).expect("mixed-width unsigned arithmetic should run");
        assert_eq!(run.exit_code, 17);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_mixed_width_signed_unsigned_arithmetic_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let a: Int8 = -5\n  let b: UInt8 = 10\n  a + b\n",
            "kea-cli-mixed-width-signed-unsigned-arithmetic",
            "kea",
        );

        let run = run_file(&source_path).expect("mixed signed/unsigned arithmetic should run");
        assert_eq!(run.exit_code, 5);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_int8_main_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int8\n  42\n",
            "kea-cli-int8-main",
            "kea",
        );

        let run = run_file(&source_path).expect("Int8 main run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_uint16_main_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> UInt16\n  let x: UInt16 = 500\n  x\n",
            "kea-cli-uint16-main",
            "kea",
        );

        let run = run_file(&source_path).expect("UInt16 main run should succeed");
        assert_eq!(run.exit_code, 500);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_int8_call_arg_coercion_exit_code() {
        let source_path = write_temp_source(
            "fn id(x: Int8) -> Int8\n  x\n\nfn main() -> Int8\n  id(42)\n",
            "kea-cli-int8-call-arg",
            "kea",
        );

        let run = run_file(&source_path).expect("Int8 call argument coercion should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_int8_try_from_some_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case Int8.try_from(42)\n    Some(v) -> v + 0\n    None -> 0\n",
            "kea-cli-int8-try-from-some",
            "kea",
        );

        let run = run_file(&source_path).expect("Int8.try_from in-range should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_int8_try_from_fixed_width_input_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let x: Int8 = 42\n  case Int8.try_from(x)\n    Some(v) -> v + 0\n    None -> 0\n",
            "kea-cli-int8-try-from-int8-input",
            "kea",
        );

        let run = run_file(&source_path).expect("Int8.try_from should accept Int8 input");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_int8_try_from_none_exit_code() {
        let source_path = write_temp_source(
            "fn id(x: Int) -> Int\n  x\n\nfn main() -> Int\n  case Int8.try_from(id(200))\n    Some(_) -> 0\n    None -> 1\n",
            "kea-cli-int8-try-from-none",
            "kea",
        );

        let run = run_file(&source_path).expect("Int8.try_from out-of-range should return None");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_uint8_try_from_negative_none_exit_code() {
        let source_path = write_temp_source(
            "fn id(x: Int) -> Int\n  x\n\nfn main() -> Int\n  case UInt8.try_from(id(-1))\n    Some(_) -> 0\n    None -> 1\n",
            "kea-cli-uint8-try-from-negative",
            "kea",
        );

        let run =
            run_file(&source_path).expect("UInt8.try_from negative should return None");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_const_try_from_overflow() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case Int8.try_from(200)\n    Some(_) -> 0\n    None -> 1\n",
            "kea-cli-const-try-from-overflow",
            "kea",
        );

        let err = run_file(&source_path).expect_err("overflowing narrowing conversion should fail");
        assert!(
            err.contains("does not fit in `Int8`"),
            "expected narrowing overflow diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_try_from_non_integer_input() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  case Int8.try_from(\"oops\")\n    Some(_) -> 0\n    None -> 1\n",
            "kea-cli-try-from-non-integer",
            "kea",
        );

        let err = run_file(&source_path).expect_err("non-integer try_from should fail");
        assert!(
            err.contains("expects an integer input"),
            "expected non-integer conversion diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_unique_use_after_move() {
        let source_path = write_temp_source(
            "enum Unique a\n  Unique(a)\n\nfn consume(value: Unique Int) -> Int\n  case value\n    Unique(v) -> v\n\nfn main() -> Int\n  let u = Unique(7)\n  let first = consume(u)\n  first + consume(u)\n",
            "kea-cli-unique-use-after-move",
            "kea",
        );

        let err = run_file(&source_path).expect_err("use-after-move should fail");
        assert!(
            err.contains("use of moved value `u`"),
            "expected use-after-move diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_unique_branch_move_mismatch() {
        let source_path = write_temp_source(
            "enum Unique a\n  Unique(a)\n\nfn consume(value: Unique Int) -> Int\n  case value\n    Unique(v) -> v\n\nfn main() -> Int\n  let u = Unique(7)\n  if true\n    consume(u)\n  else\n    0\n",
            "kea-cli-unique-branch-move-mismatch",
            "kea",
        );

        let err = run_file(&source_path).expect_err("branch move mismatch should fail");
        assert!(
            err.contains("branch move mismatch for `u`"),
            "expected branch move mismatch diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_unique_capture_then_reuse() {
        let source_path = write_temp_source(
            "enum Unique a\n  Unique(a)\n\nfn consume(value: Unique Int) -> Int\n  case value\n    Unique(v) -> v\n\nfn main() -> Int\n  let u = Unique(7)\n  let f = || consume(u)\n  consume(u)\n",
            "kea-cli-unique-capture-then-reuse",
            "kea",
        );

        let err = run_file(&source_path).expect_err("captured unique reuse should fail");
        assert!(
            err.contains("use of moved value `u`"),
            "expected use-after-move diagnostic after capture, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_borrow_param_does_not_consume_caller_unique() {
        let source_path = write_temp_source(
            "enum Unique a\n  Unique(a)\n\nfn touch(borrow value: Unique Int) -> Int\n  1\n\nfn main() -> Int\n  let u = Unique(7)\n  let _ = touch(u)\n  let _ = touch(u)\n  7\n",
            "kea-cli-borrow-does-not-consume",
            "kea",
        );

        let run = run_file(&source_path).expect("borrow call should not consume caller unique");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_auto_borrow_inferred_param_does_not_consume_caller_unique() {
        let source_path = write_temp_source(
            "enum Unique a\n  Unique(a)\n\nfn touch(value: Unique Int) -> Int\n  1\n\nfn main() -> Int\n  let u = Unique(7)\n  let _ = touch(u)\n  let _ = touch(u)\n  7\n",
            "kea-cli-auto-borrow-inferred-does-not-consume",
            "kea",
        );

        let run = run_file(&source_path).expect("auto-borrow inferred call should not consume caller unique");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_auto_borrow_inference_for_consuming_parameter() {
        let source_path = write_temp_source(
            "enum Unique a\n  Unique(a)\n\nfn take(value: Unique Int) -> Int\n  case value\n    Unique(v) -> v\n\nfn main() -> Int\n  let u = Unique(7)\n  let _ = take(u)\n  let _ = take(u)\n  0\n",
            "kea-cli-auto-borrow-does-not-infer-consuming-param",
            "kea",
        );

        let err = run_file(&source_path).expect_err("consuming parameter must not be auto-borrowed");
        assert!(
            err.contains("use of moved value `u`"),
            "expected moved-value diagnostic when auto-borrow should not apply, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_consuming_borrow_parameter_in_callee() {
        let source_path = write_temp_source(
            "enum Unique a\n  Unique(a)\n\nfn take(value: Unique Int) -> Int\n  case value\n    Unique(v) -> v\n\nfn bad(borrow value: Unique Int) -> Int\n  take(value)\n",
            "kea-cli-borrow-callee-consume-rejected",
            "kea",
        );

        let err = run_file(&source_path).expect_err("consuming borrowed parameter should fail");
        assert!(
            err.contains("borrowed value `value` cannot be consumed"),
            "expected borrow consumption diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_returning_borrow_parameter() {
        let source_path = write_temp_source(
            "enum Unique a\n  Unique(a)\n\nfn leak(borrow value: Unique Int) -> Unique Int\n  value\n",
            "kea-cli-borrow-return-escape-rejected",
            "kea",
        );

        let err = run_file(&source_path).expect_err("returning borrowed parameter should fail");
        assert!(
            err.contains("borrowed value `value` cannot be consumed"),
            "expected borrow escape diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_capturing_borrow_parameter() {
        let source_path = write_temp_source(
            "enum Unique a\n  Unique(a)\n\nfn leak_capture(borrow value: Unique Int) -> fn() -> Int\n  ||\n    case value\n      Unique(v) -> v\n",
            "kea-cli-borrow-capture-escape-rejected",
            "kea",
        );

        let err = run_file(&source_path).expect_err("capturing borrowed parameter should fail");
        assert!(
            err.contains("borrowed value `value` cannot be consumed"),
            "expected borrow capture diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_qualified_borrow_call_does_not_consume_unique() {
        let project_dir = temp_project_dir("kea-cli-qualified-borrow");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        std::fs::write(
            src_dir.join("helper.kea"),
            "enum Unique a\n  Unique(a)\n\nfn new(x: Int) -> Unique Int\n  Unique(x)\n\nfn touch(borrow value: Unique Int) -> Int\n  1\n",
        )
        .expect("helper module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Helper\n\nfn main() -> Int\n  let u = Helper.new(7)\n  let _ = Helper.touch(u)\n  let _ = Helper.touch(u)\n  7\n",
        )
        .expect("app module write should succeed");

        let run = run_file(&app_path).expect("qualified borrow call should not consume unique");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_qualified_auto_borrow_inferred_call_does_not_consume_unique() {
        let project_dir = temp_project_dir("kea-cli-qualified-auto-borrow");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");

        std::fs::write(
            src_dir.join("helper.kea"),
            "enum Unique a\n  Unique(a)\n\nfn new(x: Int) -> Unique Int\n  Unique(x)\n\nfn touch(value: Unique Int) -> Int\n  1\n",
        )
        .expect("helper module write should succeed");
        let app_path = src_dir.join("app.kea");
        std::fs::write(
            &app_path,
            "use Helper\n\nfn main() -> Int\n  let u = Helper.new(7)\n  let _ = Helper.touch(u)\n  let _ = Helper.touch(u)\n  7\n",
        )
        .expect("app module write should succeed");

        let run =
            run_file(&app_path).expect("qualified auto-borrow inferred call should not consume unique");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_and_execute_wrapping_add_method_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  20.wrapping_add(22)\n",
            "kea-cli-wrapping-add",
            "kea",
        );

        let run = run_file(&source_path).expect("wrapping-add run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_wrapping_sub_method_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  100.wrapping_sub(58)\n",
            "kea-cli-wrapping-sub",
            "kea",
        );

        let run = run_file(&source_path).expect("wrapping-sub run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_wrapping_mul_method_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  6.wrapping_mul(7)\n",
            "kea-cli-wrapping-mul",
            "kea",
        );

        let run = run_file(&source_path).expect("wrapping-mul run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_popcount_method_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  0b101011.popcount()\n",
            "kea-cli-popcount",
            "kea",
        );

        let run = run_file(&source_path).expect("popcount run should succeed");
        assert_eq!(run.exit_code, 4);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_leading_zeros_method_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  0b1000.leading_zeros()\n",
            "kea-cli-leading-zeros",
            "kea",
        );

        let run = run_file(&source_path).expect("leading_zeros run should succeed");
        assert_eq!(run.exit_code, 60);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_trailing_zeros_method_exit_code() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  0b1000.trailing_zeros()\n",
            "kea-cli-trailing-zeros",
            "kea",
        );

        let run = run_file(&source_path).expect("trailing_zeros run should succeed");
        assert_eq!(run.exit_code, 3);

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
            "fn apply(f: fn(Int) -> Int, x: Int) -> Int\n  f(x)\n\nfn main() -> Int\n  apply(|x| x + 1, 41)\n",
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
            "fn main() -> Int\n  (|x| x + 1)(41)\n",
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
            "struct Box\n  n: Int\n\nfn churn(i: Int, acc: Int) -> Int\n  if i == 0\n    acc\n  else\n    let b = Box { n: i }\n    churn(i - 1, acc + b.n - i)\n\nfn main() -> Int\n  churn(5000, 0)\n",
            "kea-cli-refcount-churn",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 0);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_emits_release_ops_for_allocation_churn_program() {
        let project_dir = temp_project_dir("kea-cli-refcount-stats");
        let src_dir = project_dir.join("src");
        let stdlib_dir = project_dir.join("stdlib");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");
        std::fs::create_dir_all(&stdlib_dir).expect("stdlib dir should be created");
        std::fs::write(stdlib_dir.join("prelude.kea"), "fn ping() -> Int\n  7\n")
            .expect("prelude module write should succeed");
        std::fs::write(
            stdlib_dir.join("show.kea"),
            "trait Show a\n  fn show(value: a) -> String\n\nfn show(value: Int) -> String\n  \"0\"\n",
        )
        .expect("show module write should succeed");

        let source_path = src_dir.join("app.kea");
        std::fs::write(
            &source_path,
            "struct Box\n  n: Int\n\nfn churn(i: Int, acc: Int) -> Int\n  if i == 0\n    acc\n  else\n    let b = Box { n: i }\n    churn(i - 1, acc + b.n - i)\n\nfn main() -> Int\n  churn(1024, 0)\n",
        )
        .expect("app module write should succeed");

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

        let _ = std::fs::remove_dir_all(project_dir);
    }

    #[test]
    fn compile_elides_heap_alias_retain_release_churn_in_stats() {
        let source_path = write_temp_source(
            "fn main() -> Int\n  let s = \"x\"\n  let t = s\n  1\n",
            "kea-cli-alias-rc-fusion-stats",
            "kea",
        );

        let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
        let retain_count: usize = compiled
            .stats
            .per_function
            .iter()
            .map(|f| f.retain_count)
            .sum();
        let release_count: usize = compiled
            .stats
            .per_function
            .iter()
            .map(|f| f.release_count)
            .sum();

        assert_eq!(
            retain_count, 0,
            "expected retain/release fusion to remove heap alias churn, stats: {:?}",
            compiled.stats
        );
        assert!(
            release_count > 0,
            "expected at least one release to preserve heap lifecycle, stats: {:?}",
            compiled.stats
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_elides_linear_heap_alias_chain_retain_churn_in_stats() {
        let source_path = write_temp_source(
            "struct Box\n  n: Int\n\nfn main() -> Int\n  let b0 = Box { n: 1 }\n  let b1 = b0\n  let b2 = b1\n  let b3 = b2\n  b3.n\n",
            "kea-cli-linear-alias-chain-rc-fusion-stats",
            "kea",
        );

        let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
        let retain_count: usize = compiled
            .stats
            .per_function
            .iter()
            .map(|f| f.retain_count)
            .sum();
        let release_count: usize = compiled
            .stats
            .per_function
            .iter()
            .map(|f| f.release_count)
            .sum();

        assert_eq!(
            retain_count, 0,
            "expected linear alias ownership transfer to avoid retain churn, stats: {:?}",
            compiled.stats
        );
        assert!(
            release_count > 0,
            "expected release ops to remain for heap lifecycle balance, stats: {:?}",
            compiled.stats
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(
            run.exit_code, 1,
            "linear alias chain should preserve observable value semantics"
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
            "fn main() -> Int\n  let f = |x| x + 1\n  f(41)\n",
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
            "fn make_adder(y: Int) -> fn(Int) -> Int\n  |x| x + y\n\nfn main() -> Int\n  let add2 = make_adder(2)\n  add2(40)\n",
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
            "fn make_adder(y: Int) -> fn(Int) -> Int\n  |x| x + y\n\nfn main() -> Int\n  make_adder(2)(40)\n",
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
            "fn apply(f: fn(Int) -> Int, x: Int) -> Int\n  f(x)\n\nfn make_adder(y: Int) -> fn(Int) -> Int\n  |x| x + y\n\nfn main() -> Int\n  apply(make_adder(2), 40)\n",
            "kea-cli-escaping-capturing-lambda",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_multiple_closures_capture_same_heap_value_exit_code() {
        let source_path = write_temp_source(
            "use List\n\nfn main() -> Int\n  let xs = List.Cons(1, List.Cons(2, List.Nil))\n  let f = || List.length(xs)\n  let g = || List.length(xs) + 1\n  f() + g()\n",
            "kea-cli-multi-closure-shared-capture",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 5);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_reject_nested_lambda_returning_lambda_in_local_binding() {
        let source_path = write_temp_source(
            "fn outer(a: Int) -> fn(Int) -> Int\n  let make = |b|\n    |c| a + b + c\n  make(30)\n\nfn main() -> Int\n  let f = outer(10)\n  f(2)\n",
            "kea-cli-nested-closure-three-scope-capture",
            "kea",
        );

        let err = run_file(&source_path)
            .expect_err("nested lambda returning lambda should currently fail in lowering");
        assert!(
            err.contains("non-unit function returned without value"),
            "expected current nested-lambda lowering diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_closure_capture_and_post_capture_use_of_heap_value_exit_code() {
        let source_path = write_temp_source(
            "use List\n\nfn main() -> Int\n  let xs = List.Cons(1, List.Cons(2, List.Cons(3, List.Nil)))\n  let f = || List.length(xs)\n  let direct = List.length(xs)\n  f() + direct\n",
            "kea-cli-closure-capture-post-use-heap",
            "kea",
        );

        let run = run_file(&source_path).expect("capture plus direct heap use should run");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_log_with_collected_logs_high_volume_exit_code() {
        let source_path = write_temp_source(
            "use Log\nuse List\n\nfn emit(n: Int) -[Log]> Unit\n  if n == 0\n    ()\n  else\n    Log.info(\"x\")\n    emit(n - 1)\n\nfn run() -[Log]> Int\n  emit(200)\n  7\n\nfn main() -> Int\n  let pair = Log.with_collected_logs(run)\n  let value = pair.0\n  let logs = pair.1\n  if value == 7 and List.length(logs) == 200\n    42\n  else\n    0\n",
            "kea-cli-log-with-collected-high-volume",
            "kea",
        );

        let run = run_file(&source_path).expect("high-volume log collection should run");
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
    fn compile_and_execute_state_tail_handler_count_to_exit_code() {
        let source_path = write_temp_source(
            "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn count_to(n: Int) -[State Int]> Int\n  let i = State.get()\n  if i >= n\n    i\n  else\n    State.put(i + 1)\n    count_to(n)\n\nfn main() -> Int\n  handle count_to(10)\n    State.get() -> resume 0\n    State.put(s) -> resume ()\n",
            "kea-cli-state-tail-handler-count-to",
            "kea",
        );

        let run = run_file(&source_path).expect("state handler run should succeed");
        assert_eq!(run.exit_code, 10);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_state_tail_handler_count_to_one_million_exit_code() {
        let source_path = write_temp_source(
            "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn count_to(n: Int) -[State Int]> Int\n  let i = State.get()\n  if i >= n\n    i\n  else\n    State.put(i + 1)\n    count_to(n)\n\nfn main() -> Int\n  handle count_to(1000000)\n    State.get() -> resume 0\n    State.put(s) -> resume ()\n",
            "kea-cli-state-tail-handler-count-to-1m",
            "kea",
        );

        let run = run_file(&source_path).expect("state handler 1M run should succeed");
        assert_eq!(run.exit_code, 1_000_000);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_state_tail_handler_count_to_marks_tail_self_call_in_stats() {
        let source_path = write_temp_source(
            "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn count_to(n: Int) -[State Int]> Int\n  let i = State.get()\n  if i >= n\n    i\n  else\n    State.put(i + 1)\n    count_to(n)\n\nfn main() -> Int\n  handle count_to(10)\n    State.get() -> resume 0\n    State.put(s) -> resume ()\n",
            "kea-cli-state-tail-handler-tail-stats",
            "kea",
        );

        let artifact =
            compile_file(&source_path, CodegenMode::Aot).expect("compile should succeed");
        let count_to_stats = artifact
            .stats
            .per_function
            .iter()
            .find(|stats| stats.function.contains("count_to"))
            .expect("expected stats entry for count_to");
        assert!(
            count_to_stats.tail_self_call_count > 0,
            "expected tail self-call detection in count_to, stats: {:?}",
            artifact.stats.per_function
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_nested_state_handler_inner_shadows_outer_exit_code() {
        let source_path = write_temp_source(
            "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn read_state() -[State Int]> Int\n  State.get()\n\nfn run_inner() -[State Int]> Int\n  handle read_state()\n    State.get() -> resume 2\n    State.put(s) -> resume ()\n\nfn main() -> Int\n  handle run_inner()\n    State.get() -> resume 9\n    State.put(s) -> resume ()\n",
            "kea-cli-state-nested-handler-shadow",
            "kea",
        );

        let run = run_file(&source_path).expect("nested state handler run should succeed");
        assert_eq!(run.exit_code, 2);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_handle_then_clause_transforms_result_exit_code() {
        let source_path = write_temp_source(
            "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn count_to(n: Int) -[State Int]> Int\n  let i = State.get()\n  if i >= n\n    i\n  else\n    State.put(i + 1)\n    count_to(n)\n\nfn main() -> Int\n  let pair = handle count_to(5)\n    State.get() -> resume 0\n    State.put(s) -> resume ()\n    then result ->\n      result + 100\n  pair\n",
            "kea-cli-handle-then-transform",
            "kea",
        );

        let run = run_file(&source_path).expect("handle then run should succeed");
        assert_eq!(run.exit_code, 105);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_log_tail_handler_resume_unit_exit_code() {
        let source_path = write_temp_source(
            "effect Log\n  fn log(msg: Int) -> Unit\n\nfn greet() -[Log]> Int\n  Log.log(7)\n  11\n\nfn main() -> Int\n  handle greet()\n    Log.log(msg) -> resume ()\n",
            "kea-cli-log-tail-handler",
            "kea",
        );

        let run = run_file(&source_path).expect("log handler run should succeed");
        assert_eq!(run.exit_code, 11);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_reader_tail_handler_resume_value_exit_code() {
        let source_path = write_temp_source(
            "effect Reader C\n  fn ask() -> C\n\nfn read() -[Reader Int]> Int\n  Reader.ask()\n\nfn main() -> Int\n  handle read()\n    Reader.ask() -> resume 42\n",
            "kea-cli-reader-tail-handler",
            "kea",
        );

        let run = run_file(&source_path).expect("reader handler run should succeed");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_effectful_named_callback_parameter_exit_code() {
        let source_path = write_temp_source(
            "effect Reader C\n  fn ask() -> C\n\nfn with_reader(env: C, f: fn() -[Reader C]> Int) -> Int\n  handle f()\n    Reader.ask() -> resume env\n\nfn app() -[Reader Int]> Int\n  Reader.ask() + 1\n\nfn main() -> Int\n  with_reader(41, app)\n",
            "kea-cli-effectful-named-callback",
            "kea",
        );

        let run = run_file(&source_path).expect("effectful named callback should run");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_effectful_with_callback_lambda_exit_code() {
        let source_path = write_temp_source(
            "effect Reader C\n  fn ask() -> C\n\nfn with_reader(env: C, @with f: fn() -[Reader C]> Int) -> Int\n  handle f()\n    Reader.ask() -> resume env\n\nfn main() -> Int\n  with with_reader(41)\n  Reader.ask() + 1\n",
            "kea-cli-effectful-with-callback-lambda",
            "kea",
        );

        let run = run_file(&source_path).expect("effectful with-callback lambda should run");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_effectful_generic_callback_return_exit_code() {
        let source_path = write_temp_source(
            "effect Reader C\n  fn ask() -> C\n\nfn with_reader(env: C, f: fn() -[Reader C]> T) -> T\n  handle f()\n    Reader.ask() -> resume env\n\nfn app() -[Reader Int]> Int\n  Reader.ask() + 1\n\nfn main() -> Int\n  with_reader(41, app)\n",
            "kea-cli-effectful-generic-callback-return",
            "kea",
        );

        let run = run_file(&source_path).expect("effectful generic callback should run");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_handler_returns_closure_capturing_effect_value_exit_code() {
        let source_path = write_temp_source(
            "effect Reader C\n  fn ask() -> C\n\nfn make_adder() -[Reader Int]> fn(Int) -> Int\n  let base = Reader.ask()\n  |x| x + base\n\nfn main() -> Int\n  let add = handle make_adder()\n    Reader.ask() -> resume 40\n  add(2)\n",
            "kea-cli-handler-returns-capturing-closure",
            "kea",
        );

        let run = run_file(&source_path).expect("handler-returned closure should run");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_reject_handler_resume_with_closure_capturing_clause_arg_in_compiled_lowering() {
        let source_path = write_temp_source(
            "effect Factory\n  fn build(seed: Int) -> fn(Int) -> Int\n\nfn program() -[Factory]> fn(Int) -> Int\n  Factory.build(40)\n\nfn main() -> Int\n  let add = handle program()\n    Factory.build(seed) -> resume (|x| x + seed)\n  add(2)\n",
            "kea-cli-handler-resume-closure-captures-clause-arg",
            "kea",
        );

        let err = run_file(&source_path).expect_err(
            "compiled handler lowering should currently reject effect ops returning closures",
        );
        assert!(
            err.contains("missing handler operation plan for effect `Factory`"),
            "expected missing handler-operation-plan diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_log_side_effecting_handler_clause_exit_code() {
        let source_path = write_temp_source(
            "effect IO\n  fn stdout(msg: String) -> Unit\n\neffect Log\n  fn info(msg: String) -> Unit\n\nfn program() -[Log]> Int\n  Log.info(\"hello\")\n  7\n\nfn with_stdout_logger(f: fn() -[Log]> Int) -[IO]> Int\n  handle f()\n    Log.info(msg) ->\n      IO.stdout(msg)\n      resume ()\n\nfn main() -[IO]> Int\n  with_stdout_logger(program)\n",
            "kea-cli-log-side-effecting-handler-clause",
            "kea",
        );

        let run = run_file(&source_path).expect("side-effecting log handler should run");
        assert_eq!(run.exit_code, 7);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_handle_then_clause_reads_handled_state_exit_code() {
        let source_path = write_temp_source(
            "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn bump() -[State Int]> Int\n  let s = State.get()\n  State.put(s + 1)\n  State.get()\n\nfn main() -> Int\n  let result = handle bump()\n    State.get() -> resume 41\n    State.put(next) -> resume ()\n    then value ->\n      State.get()\n  result\n",
            "kea-cli-handle-then-reads-state",
            "kea",
        );

        let run = run_file(&source_path).expect("handle then should read handled state");
        assert_eq!(run.exit_code, 42);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_generic_two_op_tail_handler_exit_code() {
        let source_path = write_temp_source(
            "effect Counter\n  fn read() -> Int\n  fn write(next: Int) -> Unit\n\nfn count_to(n: Int) -[Counter]> Int\n  let i = Counter.read()\n  if i >= n\n    i\n  else\n    Counter.write(i + 1)\n    count_to(n)\n\nfn main() -> Int\n  handle count_to(6)\n    Counter.read() -> resume 0\n    Counter.write(next) -> resume ()\n",
            "kea-cli-generic-two-op-tail-handler",
            "kea",
        );

        let run = run_file(&source_path).expect("generic two-op handler run should succeed");
        assert_eq!(run.exit_code, 6);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_generic_two_getter_tail_handler_exit_code() {
        let source_path = write_temp_source(
            "effect Foo\n  fn a() -> Int\n  fn b() -> Int\n\nfn body() -[Foo]> Int\n  Foo.a() + Foo.b()\n\nfn main() -> Int\n  handle body()\n    Foo.a() -> resume 10\n    Foo.b() -> resume 2\n",
            "kea-cli-generic-two-getter-tail-handler",
            "kea",
        );

        let run = run_file(&source_path).expect("generic two-getter handler run should succeed");
        assert_eq!(run.exit_code, 12);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_nested_handlers_for_different_effects_exit_code() {
        let source_path = write_temp_source(
            "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\neffect Log\n  fn log(msg: Int) -> Unit\n\nfn count_with_log(n: Int) -[State Int, Log]> Int\n  let i = State.get()\n  Log.log(i)\n  if i >= n\n    i\n  else\n    State.put(i + 1)\n    count_with_log(n)\n\nfn run_state(n: Int) -[Log]> Int\n  handle count_with_log(n)\n    State.get() -> resume 0\n    State.put(next) -> resume ()\n\nfn main() -> Int\n  handle run_state(4)\n    Log.log(msg) -> resume ()\n",
            "kea-cli-nested-handlers-different-effects",
            "kea",
        );

        let run = run_file(&source_path).expect("nested different-effect handlers should run");
        assert_eq!(run.exit_code, 4);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_reject_non_tail_resumptive_clause_body_with_effects() {
        let source_path = write_temp_source(
            "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\neffect Log\n  fn log(msg: Int) -> Unit\n\nfn f() -[State Int, Log]> Int\n  State.get()\n\nfn run_state() -[Log]> Int\n  handle f()\n    State.get() ->\n      Log.log(1)\n      resume 0\n    State.put(next) -> resume ()\n\nfn main() -> Int\n  handle run_state()\n    Log.log(msg) -> resume ()\n",
            "kea-cli-reject-non-tail-resumptive-handler-clause",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject non-tail-resumptive clause");
        assert!(
            err.contains("must be tail-resumptive (`resume ...`) for compiled lowering"),
            "expected tail-resumptive rejection, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_reject_partial_handler_clause_set_for_effect() {
        let source_path = write_temp_source(
            "effect Counter\n  fn read() -> Int\n  fn write(next: Int) -> Unit\n\nfn g() -[Counter]> Int\n  Counter.write(1)\n  Counter.read()\n\nfn main() -> Int\n  handle g()\n    Counter.read() -> resume 0\n",
            "kea-cli-reject-partial-effect-handler-clauses",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject missing effect clauses");
        assert!(
            err.contains("handler for `Counter` is missing clause(s): write"),
            "expected missing clause rejection, got: {err}"
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
            "trait Inc a\n  fn inc(x: a) -> a\n\nInt as Inc\n  fn inc(x: Int) -> Int\n    x + 1\n\nfn main() -> Int\n  Inc.inc(41)\n",
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
            "trait Inc a\n  fn inc(x: a) -> a\n\nInt as Inc\n  fn inc(x: Int) -> Int\n    x + 1\n\nFloat as Inc\n  fn inc(x: Float) -> Float\n    x + 1.0\n\nfn main() -> Int\n  Inc.inc(41)\n",
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
    fn compile_rejects_duplicate_trait_impl_for_same_type() {
        let source_path = write_temp_source(
            "trait Inc a\n  fn inc(x: a) -> a\n\nInt as Inc\n  fn inc(x: Int) -> Int\n    x + 1\n\nInt as Inc\n  fn inc(x: Int) -> Int\n    x + 2\n\nfn main() -> Int\n  0\n",
            "kea-cli-trait-duplicate-impl",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject duplicate trait impl");
        assert!(
            err.contains("already implemented") || err.contains("conflicting implementation"),
            "expected duplicate impl coherence diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_impl_missing_required_trait_method() {
        let source_path = write_temp_source(
            "trait IncDec a\n  fn inc(x: a) -> a\n  fn dec(x: a) -> a\n\nInt as IncDec\n  fn inc(x: Int) -> Int\n    x + 1\n\nfn main() -> Int\n  0\n",
            "kea-cli-trait-missing-method",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject impl missing trait method");
        assert!(
            err.contains("is missing method(s): `dec`"),
            "expected missing-trait-method diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_impl_with_extra_non_trait_method() {
        let source_path = write_temp_source(
            "trait Inc a\n  fn inc(x: a) -> a\n\nInt as Inc\n  fn inc(x: Int) -> Int\n    x + 1\n  fn dec(x: Int) -> Int\n    x - 1\n\nfn main() -> Int\n  0\n",
            "kea-cli-trait-extra-method",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject impl extra trait method");
        assert!(
            err.contains("has extra method(s) not in trait: `dec`"),
            "expected extra-trait-method diagnostic, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_impl_method_return_type_mismatch_even_when_unused() {
        let source_path = write_temp_source(
            "trait Inc a\n  fn inc(x: a) -> a\n\nInt as Inc\n  fn inc(x: Int) -> String\n    \"oops\"\n\nfn main() -> Int\n  0\n",
            "kea-cli-trait-return-type-mismatch",
            "kea",
        );

        let err = run_file(&source_path)
            .expect_err("run should reject impl return type mismatch at registration time");
        assert!(
            err.contains("has incompatible type"),
            "expected impl signature mismatch diagnostic, got: {err}"
        );
        assert!(
            err.contains("expected") && err.contains("found") && err.contains("String"),
            "expected expected/found signature detail, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_impl_method_parameter_type_mismatch_even_when_unused() {
        let source_path = write_temp_source(
            "trait Inc a\n  fn inc(x: a) -> a\n\nInt as Inc\n  fn inc(x: String) -> Int\n    0\n\nfn main() -> Int\n  0\n",
            "kea-cli-trait-param-type-mismatch",
            "kea",
        );

        let err = run_file(&source_path)
            .expect_err("run should reject impl parameter type mismatch at registration time");
        assert!(
            err.contains("has incompatible type"),
            "expected impl signature mismatch diagnostic, got: {err}"
        );
        assert!(
            err.contains("String") && err.contains("Int"),
            "expected parameter type mismatch details, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_rejects_impl_method_arity_mismatch_even_when_unused() {
        let source_path = write_temp_source(
            "trait Adder a\n  fn add(x: a, y: a) -> a\n\nInt as Adder\n  fn add(x: Int) -> Int\n    x\n\nfn main() -> Int\n  0\n",
            "kea-cli-trait-arity-mismatch",
            "kea",
        );

        let err = run_file(&source_path)
            .expect_err("run should reject impl arity mismatch at registration time");
        assert!(
            err.contains("has incompatible type"),
            "expected impl signature mismatch diagnostic, got: {err}"
        );
        assert!(
            err.contains("expected") && err.contains("found"),
            "expected expected/found signature detail, got: {err}"
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
            "enum Color\n  Red\n  Green\n\nfn main() -> Int\n  case Color.Red\n    Color.Red -> 1\n    Color.Green -> 2\n",
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
            "enum Color\n  Red\n  Green\n  Blue\n\nfn main() -> Int\n  case Color.Green\n    Color.Red | Color.Green -> 3\n    _ -> 8\n",
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
            "enum Color\n  Red\n  Green\n\nfn main() -> Int\n  case Red\n    Red -> 5\n    Green -> 9\n",
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
            "enum Color\n  Red\n  Green\n\nfn main() -> Int\n  case Color.Red\n    Color.Red when true -> 4\n    _ -> 1\n",
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
            "enum Color\n  Red\n  Green\n\nfn main() -> Int\n  case Color.Red\n    Color.Red as c when true -> 5\n    _ -> 1\n",
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
            "enum Color\n  Red\n  Green\n  Blue\n\nfn main() -> Int\n  case Color.Red\n    Color.Red | Color.Green when true -> 7\n    _ -> 1\n",
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
            "struct User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    User { age: 4, .. } -> 6\n    _ -> 2\n",
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
            "struct User\n  age: Int\n\nfn main() -> Int\n  case User { age: 7 }\n    User { age: n } -> n\n",
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
            "struct User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    User { age: years, .. } -> years + 2\n    _ -> 0\n",
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
            "struct User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    User { age, .. } -> age + 3\n    _ -> 0\n",
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
            "struct User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    User { age: years, .. } when years == 4 -> years + 10\n    _ -> 0\n",
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
            "struct User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    User { age: 3, .. } | User { age: 4, .. } -> 6\n    _ -> 2\n",
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
            "struct User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  user.age + user.score\n",
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
            "struct User\n  age: Int\n\nfn inc(self: User) -> User\n  self~{ age: self.age + 1 }\n\nfn main() -> Int\n  let user = User { age: 41 }\n  user.inc().age\n",
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
            "struct User\n  age: Int\n\nstruct Wrap\n  inner: User\n\nfn inc(self: User) -> User\n  self~{ age: self.age + 1 }\n\nfn main() -> Int\n  let wrapped = Wrap { inner: User { age: 41 } }\n  wrapped.inner.inc().age\n",
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
            "struct User\n  age: Int\n  score: Int\n\nfn get_age(u: { age: Int | r }) -> Int\n  u.age\n\nfn main() -> Int\n  let user = User { age: 41, score: 1 }\n  get_age(user)\n",
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
            "struct User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  let updated = user~{ age: user.age + 3 }\n  updated.age + updated.score\n",
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
            "struct User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  let updated = (user~{ age: user.age + 3 })~{ score: user.score + 4 }\n  updated.age + updated.score\n",
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
            "enum Flag\n  Yep(Int)\n  Nope\n\nfn make_flag() -> Flag\n  Yep(7)\n\nfn main() -> Int\n  let ignored = make_flag()\n  3\n",
            "kea-cli-sum-init",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 3);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_mutually_recursive_struct_enum_exit_code() {
        let source_path = write_temp_source(
            "struct MatchArm\n  body: HirExpr\n  tag: Int\n\nenum HirExpr\n  Lit(Int)\n  Match(HirExpr, MatchArm)\n\nfn depth(e: HirExpr) -> Int\n  case e\n    Lit(_) -> 0\n    Match(inner, _) -> 1 + depth(inner)\n\nfn main() -> Int\n  let arm = MatchArm { body: Lit(1), tag: 0 }\n  depth(Match(Lit(5), arm))\n",
            "kea-cli-jit-mutual-recursive-type-defs",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 1);

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    fn compile_and_execute_sum_payload_record_type_exit_code() {
        let source_path = write_temp_source(
            "struct User\n  age: Int\n\nenum Wrap\n  W(User)\n  N\n\nfn main() -> Int\n  case W(User { age: 7 })\n    W(u) -> u.age + 1\n    N -> 0\n",
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
            "struct User\n  age: Int\n\nenum Wrap\n  W(User)\n  N\n\nfn main() -> Int\n  case W(User { age: 7 })\n    W(User { age: n }) -> n + 2\n    N -> 0\n",
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
            "struct User\n  age: Int\n\nalias UserAlias = User\n\nenum Wrap\n  W(UserAlias)\n  N\n\nfn main() -> Int\n  case W(User { age: 7 })\n    W(u) -> u.age + 5\n    N -> 0\n",
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
            "enum Flag\n  Yep(Int)\n  Nope\n\nfn main() -> Int\n  case Yep(1 + 6)\n    Yep(n) -> n\n    Nope -> 0\n",
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
            "enum Pair\n  Pair(left: Int, right: Int)\n\nfn main() -> Int\n  case Pair(right: 1, left: 40)\n    Pair(left: a, right: b) -> a * 100 + b\n",
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
            "enum Flag\n  Yep(Int)\n  Nope\n\nfn main() -> Int\n  case Flag.Yep(7)\n    Flag.Yep(n) -> n\n    Flag.Nope -> 0\n",
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
            "enum Flag\n  Yep(Int)\n  Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(_) -> 11\n    Nope -> 0\n",
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
            "enum Flag\n  Yep(Int)\n  Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(n) -> n + 1\n    Nope -> 0\n",
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
            "enum Flag\n  Yep(Int)\n  Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(n) as whole -> n + 2\n    Nope -> 0\n",
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
            "enum Flag\n  Yep(Int)\n  Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(n) | Yep(n) -> n + 3\n    Nope -> 0\n",
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
            "enum Either\n  Left(Int)\n  Right(Int)\n  Nope\n\nfn main() -> Int\n  case Right(7)\n    Left(n) | Right(n) -> n + 4\n    Nope -> 0\n",
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
            "enum Pair\n  Pair(Int, Int)\n  Nope\n\nfn main() -> Int\n  case Pair(4, 6)\n    Pair(a, b) -> a + b\n    Nope -> 0\n",
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
            "enum Flag\n  Yep(Int)\n  Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(7) -> 14\n    Nope -> 0\n",
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
            "enum Pair\n  Pair(Int, Int)\n  Nope\n\nfn main() -> Int\n  case Pair(1, 6)\n    Pair(1, b) -> b + 1\n    Nope -> 0\n",
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
            "enum Maybe a\n  Just(a)\n  Nothing\n\nfn main() -> Int\n  case Just(Just(7))\n    Just(Just(n)) -> n + 8\n    _ -> 0\n",
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
            "enum Inner\n  A(Int)\n  B(Int)\nenum Outer\n  Wrap(Inner)\n  End\n\nfn main() -> Int\n  case Wrap(B(7))\n    Wrap(A(n) | B(n)) -> n + 12\n    _ -> 0\n",
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
            "enum Flag\n  Yep(Int)\n  Nope\n\nfn main() -> Int\n  case Yep(7)\n    Yep(n) as whole when n == 7 -> n + 5\n    Yep(_) -> 1\n    Nope -> 0\n",
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
            "enum Either\n  Left(Int)\n  Right(Int)\n  Nope\n\nfn main() -> Int\n  case Right(7)\n    Left(n) | Right(n) when n > 0 -> n + 6\n    Left(_) | Right(_) -> 1\n    Nope -> 0\n",
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
