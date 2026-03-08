
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
            input: Some(PathBuf::from("main.kea")),
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
            input: Some(PathBuf::from("suite.kea")),
        }
    );
}

#[test]
fn parse_mcp_command() {
    let args = vec!["kea".to_string(), "mcp".to_string()];
    let command = parse_cli(&args).expect("cli parse should succeed");
    assert_eq!(
        command,
        Command::Mcp {
            show_help: false,
            show_version: false,
        }
    );
}

#[test]
fn parse_mcp_help_command() {
    let args = vec!["kea".to_string(), "mcp".to_string(), "--help".to_string()];
    let command = parse_cli(&args).expect("cli parse should succeed");
    assert_eq!(
        command,
        Command::Mcp {
            show_help: true,
            show_version: false,
        }
    );
}

#[test]
fn discover_package_test_files_finds_tests_and_src_test_suffixes() {
    let project_dir = temp_project_dir("kea-cli-package-test-discovery");
    let src_dir = project_dir.join("src");
    let nested_src = src_dir.join("unit");
    let tests_dir = project_dir.join("tests");
    std::fs::create_dir_all(&nested_src).expect("nested source dir should be created");
    std::fs::create_dir_all(&tests_dir).expect("tests dir should be created");

    std::fs::write(src_dir.join("main.kea"), "fn main() -> Int\n  0\n")
        .expect("main file write should succeed");
    std::fs::write(src_dir.join("alpha_test.kea"), "test \"alpha\"\n  ()\n")
        .expect("alpha test file write should succeed");
    std::fs::write(nested_src.join("beta_test.kea"), "test \"beta\"\n  ()\n")
        .expect("beta test file write should succeed");
    std::fs::write(src_dir.join("helper.kea"), "fn helper() -> Unit\n  ()\n")
        .expect("helper file write should succeed");
    std::fs::write(tests_dir.join("integration.kea"), "test \"integration\"\n  ()\n")
        .expect("integration test file write should succeed");
    std::fs::write(tests_dir.join("README.md"), "ignored").expect("README write should succeed");

    let discovered = discover_package_test_files(&project_dir).expect("test discovery should succeed");
    let mut relative = discovered
        .iter()
        .map(|path| {
            path.strip_prefix(&project_dir)
                .expect("path should be inside project")
                .to_path_buf()
        })
        .collect::<Vec<_>>();
    relative.sort();
    assert_eq!(
        relative,
        vec![
            PathBuf::from("src/alpha_test.kea"),
            PathBuf::from("src/unit/beta_test.kea"),
            PathBuf::from("tests/integration.kea"),
        ]
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn resolve_test_targets_preserves_explicit_file_selection() {
    let explicit = PathBuf::from("tests/suite.kea");
    let targets =
        resolve_test_targets(Some(explicit.clone())).expect("explicit test input resolution should succeed");
    assert_eq!(
        targets,
        TestTargets {
            files: vec![explicit],
            package_dir: None,
        }
    );
}

#[test]
fn resolve_test_targets_without_input_discovers_package_files_from_manifest_root() {
    let project_dir = temp_project_dir("kea-cli-package-test-targets-from-manifest");
    let src_dir = project_dir.join("src");
    let tests_dir = project_dir.join("tests");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::create_dir_all(&tests_dir).expect("tests dir should be created");

    std::fs::write(
        project_dir.join("kea.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n",
    )
    .expect("manifest write should succeed");
    std::fs::write(src_dir.join("main_test.kea"), "test \"unit\"\n  ()\n")
        .expect("src test write should succeed");
    std::fs::write(tests_dir.join("integration.kea"), "test \"integration\"\n  ()\n")
        .expect("integration test write should succeed");

    let targets = resolve_test_targets_from_cwd(None, &src_dir)
        .expect("manifest-root test target resolution should succeed");
    let canonical_project_dir =
        std::fs::canonicalize(&project_dir).expect("project path should canonicalize");
    assert_eq!(
        targets.package_dir.as_deref(),
        Some(canonical_project_dir.as_path())
    );
    let mut relative = targets
        .files
        .iter()
        .map(|path| {
            path.strip_prefix(&canonical_project_dir)
                .expect("target path should be inside project")
                .to_path_buf()
        })
        .collect::<Vec<_>>();
    relative.sort();
    assert_eq!(
        relative,
        vec![
            PathBuf::from("src/main_test.kea"),
            PathBuf::from("tests/integration.kea"),
        ]
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn run_test_file_resolves_dev_dependencies_for_package_tests() {
    let project_dir = temp_project_dir("kea-cli-package-dev-deps-for-test");
    let src_dir = project_dir.join("src");
    let deps_dir = project_dir.join("deps").join("quickcheck");
    let deps_src = deps_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::create_dir_all(&deps_src).expect("dependency source dir should be created");

    std::fs::write(
        project_dir.join("kea.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n\n[dev-dependencies]\nquickcheck = { path = \"deps/quickcheck\" }\n",
    )
    .expect("root manifest write should succeed");
    std::fs::write(
        deps_dir.join("kea.toml"),
        "[package]\nname = \"quickcheck\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n",
    )
    .expect("dependency manifest write should succeed");
    std::fs::write(deps_src.join("quickcheck.kea"), "pub fn answer() -> Int\n  42\n")
        .expect("dependency module write should succeed");
    let test_path = src_dir.join("main_test.kea");
    std::fs::write(
        &test_path,
        "use Test\nuse Quickcheck\n\ntest \"dev dependency available in tests\"\n  Test.assert(Quickcheck.answer() == 42)\n",
    )
    .expect("test module write should succeed");

    let run = run_test_file(&test_path).expect("test run should succeed");
    assert_eq!(run.cases.len(), 1);
    assert!(run.cases[0].passed, "expected test to pass with dev deps");

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn run_file_excludes_dev_dependencies_outside_test_mode() {
    let project_dir = temp_project_dir("kea-cli-package-dev-deps-build-scope");
    let src_dir = project_dir.join("src");
    let deps_dir = project_dir.join("deps").join("quickcheck");
    let deps_src = deps_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::create_dir_all(&deps_src).expect("dependency source dir should be created");

    std::fs::write(
        project_dir.join("kea.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n\n[dev-dependencies]\nquickcheck = { path = \"deps/quickcheck\" }\n",
    )
    .expect("root manifest write should succeed");
    std::fs::write(
        deps_dir.join("kea.toml"),
        "[package]\nname = \"quickcheck\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n",
    )
    .expect("dependency manifest write should succeed");
    std::fs::write(deps_src.join("quickcheck.kea"), "pub fn answer() -> Int\n  42\n")
        .expect("dependency module write should succeed");
    let app_path = src_dir.join("main.kea");
    std::fs::write(
        &app_path,
        "use Quickcheck\n\nfn main() -> Int\n  Quickcheck.answer()\n",
    )
    .expect("app module write should succeed");

    let err = run_file(&app_path).expect_err("dev dependencies should not resolve in run mode");
    assert!(
        err.contains("module `Quickcheck` not found"),
        "expected unresolved module error, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn parse_run_without_input_uses_manifest_entry() {
    let args = vec!["kea".to_string(), "run".to_string()];
    let command = parse_cli(&args).expect("cli parse should succeed");
    assert_eq!(command, Command::Run { input: None });
}

#[test]
fn parse_pkg_add_path_dependency() {
    let args = vec![
        "kea".to_string(),
        "pkg".to_string(),
        "add".to_string(),
        "utils".to_string(),
        "--path".to_string(),
        "../utils".to_string(),
    ];
    let command = parse_cli(&args).expect("pkg add parse should succeed");
    assert_eq!(
        command,
        Command::Pkg {
            command: PackageCommand::Add {
                name: "utils".to_string(),
                spec: DepSpec::Path {
                    path: PathBuf::from("../utils"),
                },
            },
        }
    );
}

#[test]
fn parse_pkg_update_single_dependency() {
    let args = vec![
        "kea".to_string(),
        "pkg".to_string(),
        "update".to_string(),
        "json".to_string(),
    ];
    let command = parse_cli(&args).expect("pkg update parse should succeed");
    assert_eq!(
        command,
        Command::Pkg {
            command: PackageCommand::Update {
                dependency: Some("json".to_string()),
            },
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
        "char_tests.kea",
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
#[cfg(not(target_os = "windows"))]
fn run_stdlib_vector_tests() {
    let vector_kea = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../stdlib/vector.kea");
    let run = run_test_file(&vector_kea).expect("stdlib/vector.kea should compile and run");
    let failures: Vec<_> = run
        .cases
        .iter()
        .filter(|c| !c.passed)
        .map(|c| {
            format!(
                "{} ({})",
                c.name,
                c.error.as_deref().unwrap_or("unknown failure")
            )
        })
        .collect();
    assert!(
        failures.is_empty(),
        "stdlib/vector.kea test failures:\n{}",
        failures.join("\n")
    );
    assert!(
        !run.cases.is_empty(),
        "stdlib/vector.kea: no test declarations found"
    );
}

#[test]
fn run_algorithm_gallery_binary_search() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms/binary_search.kea");
    let run = run_test_file(&path).expect("binary_search.kea should run");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "binary_search failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests in binary_search.kea");
}

#[test]
fn run_algorithm_gallery_fnv1a() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms/fnv1a.kea");
    let run = run_test_file(&path).expect("fnv1a.kea should run");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "fnv1a failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests in fnv1a.kea");
}

#[test]
fn run_algorithm_gallery_merge_sort_basic() {
    let path = std::path::PathBuf::from("/tmp/sort_combo.kea");
    let run = run_test_file(&path).expect("merge_sort_test.kea should compile");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "merge failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests ran");
}

#[test]
fn run_algorithm_gallery_merge_sort_split_only() {
    let source = "\
use List\nuse Test\n\n\
fn split(xs: List Int) -> (List Int, List Int)\n  \
split_step(xs, xs, Nil)\n\n\
fn split_step(slow: List Int, fast: List Int, left_acc: List Int) -> (List Int, List Int)\n  \
case fast\n    \
Nil ->\n      (List.reverse(left_acc), slow)\n    \
Cons(_, Nil) ->\n      (List.reverse(left_acc), slow)\n    \
Cons(_, Cons(_, fast_tail)) ->\n      \
case slow\n        \
Nil -> (List.reverse(left_acc), Nil)\n        \
Cons(s, slow_tail) -> split_step(slow_tail, fast_tail, Cons(s, left_acc))\n\n\
test \"split even\"\n  \
let halves = split([1, 2, 3, 4])\n  \
let left = halves.0\n  \
let right = halves.1\n  \
Test.assert(List.length(left) == 2)\n  \
Test.assert(List.length(right) == 2)\n";
    let path = write_temp_source(source, "kea-merge-split", "kea");
    let run = run_test_file(&path).expect("split should compile");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "split failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests ran");
    let _ = std::fs::remove_file(path);
}

#[test]
fn run_algorithm_gallery_merge_sort_simple() {
    let source = "\
use List\nuse Test\n\n\
fn merge_acc(xs: List Int, ys: List Int, acc: List Int) -> List Int\n  \
case xs\n    \
Nil -> List.append(List.reverse(acc), ys)\n    \
Cons(x, xs_tail) ->\n      \
case ys\n        \
Nil -> List.append(List.reverse(acc), xs)\n        \
Cons(y, ys_tail) ->\n          \
if x <= y\n            \
merge_acc(xs_tail, ys, Cons(x, acc))\n          \
else\n            \
merge_acc(xs, ys_tail, Cons(y, acc))\n\n\
test \"merge simple\"\n  \
let result = merge_acc([1, 3], [2, 4], [])\n  \
Test.assert(List.length(result) == 4)\n";
    let path = write_temp_source(source, "kea-merge-simple", "kea");
    let run = run_test_file(&path).expect("merge simple should compile");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "merge failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests ran");
    let _ = std::fs::remove_file(path);
}

#[test]
fn run_algorithm_gallery_merge_sort() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms/merge_sort.kea");
    let run = run_test_file(&path).expect("merge_sort.kea should run");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "merge_sort failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests in merge_sort.kea");
}

#[test]
fn run_algorithm_gallery_welford() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms/welford.kea");
    let run = run_test_file(&path).expect("welford.kea should run");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "welford failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests in welford.kea");
}

#[test]
#[cfg(not(target_os = "windows"))]
fn run_algorithm_gallery_insertion_sort() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms/insertion_sort.kea");
    let run = run_test_file(&path).expect("insertion_sort.kea should run");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "insertion_sort failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests in insertion_sort.kea");
}

#[test]
#[cfg(not(target_os = "windows"))]
fn run_algorithm_gallery_quicksort() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms/quicksort.kea");
    let run = run_test_file(&path).expect("quicksort.kea should run");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "quicksort failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests in quicksort.kea");
}

#[test]
#[cfg(not(target_os = "windows"))]
fn run_algorithm_gallery_dot_product() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms/dot_product.kea");
    let run = run_test_file(&path).expect("dot_product.kea should run");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "dot_product failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests in dot_product.kea");
}

#[test]
#[cfg(not(target_os = "windows"))]
fn run_algorithm_gallery_ring_buffer() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms/ring_buffer.kea");
    let run = run_test_file(&path).expect("ring_buffer.kea should run");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "ring_buffer failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests in ring_buffer.kea");
}

#[test]
#[cfg(not(target_os = "windows"))]
fn run_algorithm_gallery_priority_queue() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms/priority_queue.kea");
    let run = run_test_file(&path).expect("priority_queue.kea should run");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "priority_queue failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests in priority_queue.kea");
}

#[test]
#[cfg(not(target_os = "windows"))]
fn run_algorithm_gallery_matrix_multiply() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms/matrix_multiply.kea");
    let run = run_test_file(&path).expect("matrix_multiply.kea should run");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(failures.is_empty(), "matrix_multiply failures: {:?}", failures);
    assert!(!run.cases.is_empty(), "no tests in matrix_multiply.kea");
}

#[test]
fn run_algorithm_gallery_with_kea_test_runner() {
    let cases_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/algorithms");
    let supported = [
        "binary_search.kea",
        "dot_product.kea",
        "fnv1a.kea",
        "insertion_sort.kea",
        "matrix_multiply.kea",
        "merge_sort.kea",
        "quicksort.kea",
        "priority_queue.kea",
        "ring_buffer.kea",
        "welford.kea",
    ];
    let mut case_files = std::fs::read_dir(&cases_dir)
        .expect("algorithm gallery dir should exist")
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
        "expected {} algorithm gallery files in {}, found {}",
        supported.len(),
        cases_dir.display(),
        case_files.len()
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
        "algorithm gallery failures:\n{}",
        failures.join("\n")
    );
}

// Regression: accessing .0 and .1 on the same tuple variable as function call
// arguments previously triggered an AnonRecord constraint conflict when the
// check_expr_bidir path was used for numeric field access.
#[test]
fn compile_tuple_field_access_as_function_args_typechecks() {
    let source = "\
fn pair() -> (Int, Int)\n  (40, 2)\n\nfn add(a: Int, b: Int) -> Int\n  a + b\n\nfn main() -> Int\n  let p = pair()\n  add(p.0, p.1)\n";
    let source_path = write_temp_source(source, "kea-tuple-field-args", "kea");
    let run = run_file(&source_path).expect("tuple field args should compile and run");
    assert_eq!(run.exit_code, 42, "p.0 + p.1 should equal 42");
    let _ = std::fs::remove_file(source_path);
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
        err.contains("const initializer") && err.contains("not supported yet"),
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
fn compile_and_execute_list_literal_with_stdlib_list_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-project-list-literal-stdlib");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    std::fs::write(
            &app_path,
            "use List\n\nfn main() -> Int\n  let xs = [10, 20, 30]\n  List.length(xs)\n",
        )
            .expect("app module write should succeed");

    let run = run_file(&app_path).expect("run should succeed");
    assert_eq!(run.exit_code, 3);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_and_execute_list_literal_with_pattern_match_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-project-list-literal-pattern");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    std::fs::write(
            &app_path,
            "use List\n\nfn head_or_zero(xs: List Int) -> Int\n  case xs\n    Cons(h, _) -> h\n    Nil -> 0\n\nfn main() -> Int\n  let xs = [10, 20, 30]\n  head_or_zero(xs)\n",
        )
            .expect("app module write should succeed");

    let run = run_file(&app_path).expect("run should succeed");
    assert_eq!(run.exit_code, 10);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_and_execute_empty_list_literal_with_stdlib_list_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-project-empty-list-literal");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    std::fs::write(
            &app_path,
            "use List\n\nfn main() -> Int\n  let xs: List Int = []\n  List.length(xs)\n",
        )
            .expect("app module write should succeed");

    let run = run_file(&app_path).expect("run should succeed");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_and_execute_char_literal_exit_code() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  let c = 'A'\n  65\n",
        "kea-cli-char-lit",
        "kea",
    );
    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 65);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_char_escape_newline_exit_code() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  let c = '\\n'\n  10\n",
        "kea-cli-char-escape",
        "kea",
    );
    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 10);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_io_exit_exit_code() {
    // IO.exit stores exit code in thread-local and returns; JIT runner picks it up.
    let project_dir = temp_workspace_project_dir("kea-cli-project-io-exit");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    std::fs::write(
        &app_path,
        "use IO\n\nfn main() -[IO]> Int\n  IO.exit(42)\n  0\n",
    )
    .expect("app module write should succeed");

    let run = run_file(&app_path).expect("IO.exit should compile and execute");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_and_execute_io_file_exists_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-project-io-file-exists");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    // file_exists on /tmp should return True (always exists on unix)
    std::fs::write(
        &app_path,
        "use IO\n\nfn bool_to_int(b: Bool) -> Int\n  if b\n    1\n  else\n    0\n\nfn main() -[IO]> Int\n  let exists = IO.file_exists(\"/tmp\")\n  bool_to_int(exists) + 41\n",
    )
    .expect("app module write should succeed");

    let run = run_file(&app_path).expect("IO.file_exists should compile and execute");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_and_execute_io_env_var_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-project-io-env-var");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    // env_var on a non-existent var returns empty string; check length == 0
    std::fs::write(
        &app_path,
        "use IO\nuse Text\n\nfn main() -[IO]> Int\n  let val = IO.env_var(\"__KEA_TEST_NONEXISTENT_VAR__\")\n  if Text.length(val) == 0\n    42\n  else\n    0\n",
    )
    .expect("app module write should succeed");

    let run = run_file(&app_path).expect("IO.env_var should compile and execute");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_and_execute_io_mkdir_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-project-io-mkdir");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    // mkdir creates a dir, then file_exists confirms it
    std::fs::write(
        &app_path,
        "use IO\n\nfn bool_to_int(b: Bool) -> Int\n  if b\n    1\n  else\n    0\n\nfn main() -[IO]> Int\n  IO.mkdir(\"test_output_dir\")\n  let exists = IO.file_exists(\"test_output_dir\")\n  bool_to_int(exists) + 41\n",
    )
    .expect("app module write should succeed");

    let run = run_file(&app_path).expect("IO.mkdir should compile and execute");
    assert_eq!(run.exit_code, 42);

    // cleanup
    let _ = std::fs::remove_dir_all(project_dir.join("test_output_dir"));
    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_and_execute_string_eq_exit_code() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  if \"hello\" == \"hello\"\n    42\n  else\n    0\n",
        "kea-cli-string-eq",
        "kea",
    );
    let run = run_file(&source_path).expect("string equality should work");
    assert_eq!(run.exit_code, 42);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_string_neq_exit_code() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  if \"hello\" != \"world\"\n    42\n  else\n    0\n",
        "kea-cli-string-neq",
        "kea",
    );
    let run = run_file(&source_path).expect("string inequality should work");
    assert_eq!(run.exit_code, 42);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_string_hash_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-project-string-hash");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    // Use the hash_string intrinsic directly to verify DJB2 works
    std::fs::write(
        &app_path,
        "use Hash\n\nfn main() -> Int\n  let h1 = Hash.hash_string(\"hello\")\n  let h2 = Hash.hash_string(\"hello\")\n  if h1 == h2\n    42\n  else\n    0\n",
    )
    .expect("app module write should succeed");

    let run = run_file(&app_path).expect("string hash should compile and execute");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_and_execute_map_with_int_keys_hash_eq_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-project-map-int-keys");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    std::fs::write(
        &app_path,
        "use Hash\nuse Eq\n\nfn main() -> Int\n  let m = %{1 => 10, 2 => 20}\n  42\n",
    )
    .expect("app module write should succeed");

    let run = run_file(&app_path).expect("map with Int keys should compile with Hash+Eq");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_and_execute_map_with_string_keys_hash_eq_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-project-map-string-keys");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    std::fs::write(
        &app_path,
        "use Hash\nuse Eq\n\nfn main() -> Int\n  let m = %{\"a\" => 10, \"b\" => 20}\n  42\n",
    )
    .expect("app module write should succeed");

    let run = run_file(&app_path).expect("map with String keys should compile with Hash+Eq");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_and_execute_hash_trait_int_impl_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-project-hash-trait");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    let app_path = src_dir.join("app.kea");
    std::fs::write(
            &app_path,
            "use Hash\n\nfn main() -> Int\n  Hash.hash(42)\n",
        )
            .expect("app module write should succeed");

    let run = run_file(&app_path).expect("run should succeed");
    assert_eq!(run.exit_code, 42);

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
        "use Float\n\nfn main() -> Int\n  let value = Float.fabs(-42.5)\n  if value > 42.0 and value < 43.0\n    42\n  else\n    0\n",
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
        "use Order\n\ntrait Sortable a\n  fn compare(a: a, b: a) -> Ordering\n\nfn main() -> Int\n  0\n",
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
fn compile_project_rejects_private_import_from_dependency_package() {
    let project_dir = temp_project_dir("kea-cli-package-private-import");
    let src_dir = project_dir.join("src");
    let dep_dir = project_dir.join("deps").join("json");
    let dep_src = dep_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::create_dir_all(&dep_src).expect("dependency source dir should be created");

    std::fs::write(
        project_dir.join("kea.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n\n[dependencies]\njson = { path = \"deps/json\" }\n",
    )
    .expect("root manifest write should succeed");
    std::fs::write(
        dep_dir.join("kea.toml"),
        "[package]\nname = \"json\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n",
    )
    .expect("dep manifest write should succeed");
    std::fs::write(
        dep_src.join("json.kea"),
        "pub fn encode(x: Int) -> Int\n  x\n\nfn hidden(x: Int) -> Int\n  x + 1\n",
    )
    .expect("dep module write should succeed");
    let app_path = src_dir.join("main.kea");
    std::fs::write(
        &app_path,
        "use Json.{hidden}\n\nfn main() -> Int\n  hidden(1)\n",
    )
    .expect("app module write should succeed");

    let err = run_file(&app_path).expect_err("private dependency imports should fail");
    assert!(
        err.contains("not public"),
        "expected package-boundary visibility error, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_project_rejects_private_module_qualified_access_from_dependency_package() {
    let project_dir = temp_project_dir("kea-cli-package-private-qualified-access");
    let src_dir = project_dir.join("src");
    let dep_dir = project_dir.join("deps").join("json");
    let dep_src = dep_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::create_dir_all(&dep_src).expect("dependency source dir should be created");

    std::fs::write(
        project_dir.join("kea.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n\n[dependencies]\njson = { path = \"deps/json\" }\n",
    )
    .expect("root manifest write should succeed");
    std::fs::write(
        dep_dir.join("kea.toml"),
        "[package]\nname = \"json\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n",
    )
    .expect("dep manifest write should succeed");
    std::fs::write(
        dep_src.join("json.kea"),
        "pub fn encode(x: Int) -> Int\n  x\n\nfn hidden(x: Int) -> Int\n  x + 1\n",
    )
    .expect("dep module write should succeed");
    let app_path = src_dir.join("main.kea");
    std::fs::write(&app_path, "use Json\n\nfn main() -> Int\n  Json.hidden(1)\n")
        .expect("app module write should succeed");

    let err = run_file(&app_path).expect_err("private module-qualified dependency access should fail");
    assert!(
        err.contains("not public"),
        "expected package-boundary visibility error, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn compile_project_rejects_dependency_namespace_collision_with_local_module() {
    let project_dir = temp_project_dir("kea-cli-package-namespace-collision");
    let src_dir = project_dir.join("src");
    let dep_dir = project_dir.join("deps").join("json");
    let dep_src = dep_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::create_dir_all(&dep_src).expect("dependency source dir should be created");

    std::fs::write(
        project_dir.join("kea.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n\n[dependencies]\njson = { path = \"deps/json\" }\n",
    )
    .expect("root manifest write should succeed");
    std::fs::write(
        dep_dir.join("kea.toml"),
        "[package]\nname = \"json\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n",
    )
    .expect("dep manifest write should succeed");
    std::fs::write(dep_src.join("json.kea"), "pub fn ping() -> Int\n  1\n")
        .expect("dep module write should succeed");
    std::fs::write(src_dir.join("json.kea"), "fn local() -> Int\n  0\n")
        .expect("local conflicting module write should succeed");
    let app_path = src_dir.join("main.kea");
    std::fs::write(&app_path, "fn main() -> Int\n  0\n").expect("app module write should succeed");

    let err = run_file(&app_path).expect_err("namespace collisions should fail");
    assert!(
        err.contains("dependency namespace collision"),
        "expected namespace collision error, got: {err}"
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
                let expect_success = matrix_inherent_expected(call_form, import_state, relation);
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
                    MatrixCallForm::UmsUnqualified => "let xs = Item(41)\nxs.size()".to_string(),
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
fn compile_and_execute_io_stdout_empty_string_exit_code() {
    let source_path = write_temp_source(
        "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO.stdout(\"\")\n",
        "kea-cli-io-stdout-empty",
        "kea",
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_io_stdout_very_long_string_exit_code() {
    let payload = "a".repeat(10 * 1024);
    let source = format!(
        "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO.stdout(\"{payload}\")\n"
    );
    let source_path = write_temp_source(&source, "kea-cli-io-stdout-very-long", "kea");

    let run = run_file(&source_path).expect("run should succeed for long stdout payload");
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

    let err = run_file(&source_path).expect_err("run should reject parenthesized lambda syntax");
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
        err.contains("expected declaration"),
        "expected parser declaration diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_accepts_derive_eq_on_sum_for_typechecking() {
    let source_path = write_temp_source(
        "@derive(Eq)\nenum PairBox\n  Pair(Int, Int)\n\nfn main() -> Int\n  let _same = PairBox.Pair(1, 2) == PairBox.Pair(1, 2)\n  0\n",
        "kea-cli-derive-eq-sum-structural-equality",
        "kea",
    );

    let run = run_file(&source_path).expect("run should compile and execute");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_derive_eq_semantics_on_sum_exit_code() {
    let source_path = write_temp_source(
        "use Eq\n\n@derive(Eq)\nenum PairBox\n  Pair(Int, Int)\n\nfn main() -> Int\n  let a = PairBox.Pair(1, 2)\n  let b = PairBox.Pair(1, 2)\n  let c = PairBox.Pair(2, 1)\n  if a == b and a != c\n    42\n  else\n    0\n",
        "kea-cli-derive-eq-semantics-sum",
        "kea",
    );

    let run = run_file(&source_path).expect("run should compile and execute");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_equality_without_eq_impl() {
    let source_path = write_temp_source(
        "enum PairBox\n  Pair(Int, Int)\n\nfn main() -> Int\n  if PairBox.Pair(1, 2) == PairBox.Pair(1, 2)\n    0\n  else\n    1\n",
        "kea-cli-equality-without-eq-impl",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject equality without Eq impl");
    assert!(
        err.contains("does not implement trait `Eq`"),
        "expected Eq trait-bound diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_accepts_derive_show_on_sum_declaration() {
    let source_path = write_temp_source(
        "@derive(Show)\nenum PairBox\n  Pair(Int, Int)\n\nfn main() -> Int\n  0\n",
        "kea-cli-derive-show-sum",
        "kea",
    );

    let run = run_file(&source_path).expect("run should compile and execute");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_derive_ord_on_sum_exit_code() {
    let source_path = write_temp_source(
        "use Ord\n\n@derive(Ord)\nenum Flag\n  Off\n  On\n\nfn main() -> Int\n  1\n",
        "kea-cli-derive-ord-sum",
        "kea",
    );

    let run = run_file(&source_path).expect("run should compile and execute");
    assert_eq!(run.exit_code, 1);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_derive_hash_on_sum_exit_code() {
    let source_path = write_temp_source(
        "use Hash\n\n@derive(Hash)\nenum PairBox\n  Pair(Int, Int)\n\nfn main() -> Int\n  1\n",
        "kea-cli-derive-hash-sum",
        "kea",
    );

    let run = run_file(&source_path).expect("run should compile and execute");
    assert_eq!(run.exit_code, 1);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_accepts_derive_eq_show_ord_hash_together() {
    let source_path = write_temp_source(
        "use Hash\nuse Ord\n\n@derive(Eq, Show, Ord, Hash)\nenum Flag\n  A\n  B\n\nfn main() -> Int\n  1\n",
        "kea-cli-derive-all-traits",
        "kea",
    );

    let run = run_file(&source_path).expect("run should compile and execute");
    assert_eq!(run.exit_code, 1);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_derive_ord_semantics_on_sum_exit_code() {
    let source_path = write_temp_source(
        "use Ord\nuse Order\n\n@derive(Ord)\nenum Flag\n  Off\n  On\n\nfn main() -> Int\n  let off = Flag.Off\n  let on = Flag.On\n  let lo = off.compare(on)\n  let hi = on.compare(off)\n  let eq = on.compare(on)\n  if lo.Order.is_less() and hi.Order.is_greater() and eq.Order.is_equal()\n    42\n  else\n    0\n",
        "kea-cli-derive-ord-semantics-sum",
        "kea",
    );

    let run = run_file(&source_path).expect("run should compile and execute");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_derive_hash_semantics_on_sum_exit_code() {
    let source_path = write_temp_source(
        "use Hash\n\n@derive(Hash)\nenum PairBox\n  Pair(Int, Int)\n\nfn main() -> Int\n  let a = PairBox.Pair(1, 2)\n  let b = PairBox.Pair(1, 2)\n  let c = PairBox.Pair(2, 1)\n  if a.hash() == b.hash() and a.hash() != c.hash()\n    42\n  else\n    0\n",
        "kea-cli-derive-hash-semantics-sum",
        "kea",
    );

    let run = run_file(&source_path).expect("run should compile and execute");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_derive_show_semantics_on_sum_exit_code() {
    let source_path = write_temp_source(
        "use Show\nuse Text\n\n@derive(Show)\nenum Flag\n  Off\n  On\n\nfn main() -> Int\n  let off = Flag.Off\n  let on = Flag.On\n  let a = off.show()\n  let b = on.show()\n  if a != b and Text.length(a) > 0 and Text.length(b) > 0\n    42\n  else\n    0\n",
        "kea-cli-derive-show-semantics-sum",
        "kea",
    );

    let run = run_file(&source_path).expect("run should compile and execute");
    assert_eq!(run.exit_code, 42);

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

    let err = run_file(&source_path).expect_err("run should reject unterminated interpolation");
    assert!(
        err.contains("unterminated interpolation in string"),
        "expected unterminated interpolation diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_unterminated_string_literal() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  let x = \"oops\n  0\n",
        "kea-cli-string-literal-unterminated",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject unterminated string");
    assert!(
        err.contains("unterminated string literal"),
        "expected unterminated-string diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_empty_file_without_main() {
    let source_path = write_temp_source("", "kea-cli-empty-file-no-main", "kea");

    let err = run_file(&source_path).expect_err("run should reject empty source files");
    assert!(
        err.contains("main"),
        "expected missing-main style diagnostic for empty file, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_whitespace_only_file_without_main() {
    let source_path =
        write_temp_source(" \n  \n\t\n", "kea-cli-whitespace-only-file-no-main", "kea");

    let err = run_file(&source_path).expect_err("run should reject whitespace-only source files");
    assert!(
        err.contains("main"),
        "expected missing-main style diagnostic for whitespace-only file, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_comment_only_file_without_main() {
    let source_path = write_temp_source(
        "-- only comments\n-- no declarations\n",
        "kea-cli-comment-only-file-no-main",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject comment-only source files");
    assert!(
        err.contains("main"),
        "expected missing-main style diagnostic for comment-only file, got: {err}"
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
fn compile_rejects_unexpected_eof_mid_return_type_annotation() {
    let source_path = write_temp_source(
        "fn id(x: Int) ->\n  x\n\nfn main() -> Int\n  id(1)\n",
        "kea-cli-unexpected-eof-mid-return-type",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject missing return type");
    assert!(
        err.contains("expected type"),
        "expected missing-return-type diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_unexpected_eof_mid_handler_clause_body() {
    let source_path = write_temp_source(
        "effect Ping\n  fn ask() -> Int\n\nfn run() -[Ping]> Int\n  Ping.ask()\n\nfn main() -> Int\n  handle run()\n    Ping.ask() ->\n",
        "kea-cli-unexpected-eof-mid-handler-clause",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject incomplete handler clause");
    assert!(
        err.contains("expected expression"),
        "expected incomplete-handler-clause diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_unexpected_eof_mid_case_arm_body() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  case 1\n    1 ->\n",
        "kea-cli-unexpected-eof-mid-case-arm",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject incomplete case arm");
    assert!(
        err.contains("expected expression"),
        "expected incomplete-case-arm diagnostic, got: {err}"
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
fn compile_rejects_garbage_after_valid_top_level_declaration() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  1\n\n#\n",
        "kea-cli-garbage-after-valid-decl",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject garbage trailing tokens");
    assert!(
        err.contains("unexpected character"),
        "expected garbage-token lexer diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_mismatched_parenthesis_in_expression() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  let x = (1 + 2\n  x\n",
        "kea-cli-mismatched-parenthesis",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject mismatched parentheses");
    assert!(
        err.contains("expected ')'") || err.contains("expected expression"),
        "expected mismatched-parenthesis diagnostic, got: {err}"
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
        err.contains("resume value has type") && err.contains("Int") && err.contains("String"),
        "expected resume type-mismatch diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

/// §5.13: When the body constrains `Reader Int`, the handler must resume
/// with an Int, not a String.  Shared type-variable instantiation
/// connects the body's concrete type parameter to the handler clause.
#[test]
fn compile_rejects_polymorphic_effect_resume_type_mismatch() {
    let source_path = write_temp_source(
        "effect Reader R\n  fn ask() -> R\n\nfn app() -[Reader Int]> Int\n  Reader.ask() + 1\n\nfn main() -> Int\n  handle app()\n    Reader.ask() -> resume \"bad\"\n",
        "kea-cli-poly-effect-resume-mismatch",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("should reject polymorphic effect resume type mismatch");
    assert!(
        err.contains("resume value has type"),
        "expected resume type mismatch diagnostic for polymorphic effect resume, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

/// §5.13: State effect — put constrains the type parameter, get's resume
/// must match.  Handler resumes get() with String when State is Int.
#[test]
fn compile_rejects_state_handler_resume_type_mismatch() {
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(val: S) -> Unit\n\nfn app() -[State Int]> Int\n  State.put(10)\n  State.get()\n\nfn main() -> Int\n  handle app()\n    State.get() -> resume \"bad\"\n    State.put(val) -> resume ()\n",
        "kea-cli-state-resume-mismatch",
        "kea",
    );

    let err = run_file(&source_path).expect_err("should reject State handler resume type mismatch");
    assert!(
        err.contains("resume value has type"),
        "expected resume type mismatch diagnostic for State resume, got: {err}"
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
fn compile_rejects_effect_operation_call_with_missing_required_argument() {
    let source_path = write_temp_source(
        "effect Counter\n  fn add(x: Int) -> Unit\n\nfn main() -[Counter]> Int\n  Counter.add()\n  0\n",
        "kea-cli-effect-op-missing-arg",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject missing call arguments");
    assert!(
        err.contains("missing required argument `x`"),
        "expected missing-argument diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_effect_operation_call_with_wrong_argument_type() {
    let source_path = write_temp_source(
        "effect Counter\n  fn add(x: Int) -> Unit\n\nfn main() -[Counter]> Int\n  Counter.add(\"oops\")\n  0\n",
        "kea-cli-effect-op-type-mismatch",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("run should reject effect operation argument mismatch");
    assert!(
        err.contains("type mismatch") && err.contains("Int") && err.contains("String"),
        "expected operation argument type-mismatch diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_duplicate_fail_effect_entries_with_incompatible_payloads() {
    let source_path = write_temp_source(
        "effect Fail E\n  fn fail(err: E) -> Never\n\nfn bad() -[Fail Int, Fail String]> Int\n  0\n\nfn main() -> Int\n  0\n",
        "kea-cli-effect-row-duplicate-fail-incompatible",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("run should reject incompatible duplicate Fail entries in effect row");
    assert!(
        err.contains("effect row") && err.contains("multiple incompatible `Fail` entries"),
        "expected incompatible duplicate Fail diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_accepts_parenthesized_effect_payload_type_annotation() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\neffect Echo A\n  fn echo(value: A) -> Unit\n\nfn emit(x: Unique Int) -[Echo (Unique Int)]> Unit\n  Echo.echo(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-parenthesized-effect-payload-type",
        "kea",
    );

    let run = run_file(&source_path).expect("program should compile");
    assert_eq!(run.exit_code, 0);

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
fn compile_and_execute_fip_zero_alloc_function_exit_code() {
    let source_path = write_temp_source(
        "@fip\nfn id(x: Int) -> Int\n  x\n\nfn main() -> Int\n  id(7)\n",
        "kea-cli-fip-zero-alloc",
        "kea",
    );

    let run = run_file(&source_path).expect("@fip zero-alloc function should compile and run");
    assert_eq!(run.exit_code, 7);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_return_handoff_exit_code() {
    let source_path = write_temp_source(
        "@fip\nfn forward(x: Unique Int) -> Unique Int\n  x\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-return",
        "kea",
    );

    let run = run_file(&source_path).expect("@fip unique return handoff should verify");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_alias_forward_handoff_exit_code() {
    let source_path = write_temp_source(
        "@fip\nfn alias_forward(x: Unique Int) -> Unique Int\n  let y = x\n  y\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-alias-forward",
        "kea",
    );

    let run = run_file(&source_path).expect("@fip unique alias-forward handoff should verify");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_inline_lambda_forward_exit_code() {
    let source_path = write_temp_source(
        "@fip\nfn inline_lambda_forward(x: Unique Int) -> Unique Int\n  (|y| y)(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-inline-lambda-forward",
        "kea",
    );

    let run = run_file(&source_path).expect("@fip verifier should accept inlined unique handoff");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_known_forwarder_call_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_forward_once(x: Unique Int) -> Unique Int\n  forward_once(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-known-forwarder-call",
        "kea",
    );

    let run =
        run_file(&source_path).expect("@fip verifier should accept known safe forwarder calls");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_known_forwarder_with_passthrough_arg_exit_code() {
    let source_path = write_temp_source(
        "fn forward_with_seed(seed: Int, x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_forward_with_seed(x: Unique Int) -> Unique Int\n  forward_with_seed(42, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-known-forwarder-with-passthrough-arg",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept verified forwarders where the unique handoff parameter is not arg0",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_module_alias_forwarder_with_passthrough_arg_exit_code() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-module-alias-forwarder-passthrough-arg");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_with_seed(seed: Int, x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
            &source_path,
            "use Alpha as A\n\n@fip\nfn call_forward_with_seed(x: Unique Int) -> Unique Int\n  A.forward_with_seed(42, x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier should accept module-alias forwarders with passthrough arguments when the unique handoff slot is verified",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_value_call_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  f(x)\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder(forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-call",
        "kea",
    );

    let run = run_file(&source_path).expect(
            "@fip verifier should accept higher-order forwarding when the forwarder is a known-safe function item",
        );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_with_passthrough_alias_let_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_with_seed(seed: Int, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed_alias = seed\n  let y = x\n  f(y)\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_with_seed(42, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-passthrough-alias-let",
        "kea",
    );

    let run = run_file(&source_path).expect(
            "@fip verifier should accept higher-order wrappers with benign alias lets for passthrough params before the unique handoff",
        );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_with_passthrough_alias_let_exit_code()
{
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-module-alias-passthrough-alias-let",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_with_seed(seed: Int, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed_alias = seed\n  let y = x\n  f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
            &source_path,
            "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_forwarder_with_seed(42, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers with passthrough alias lets",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_with_passthrough_alias_let_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-passthrough-alias-let");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_with_seed(seed: Int, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed_alias = seed\n  let y = x\n  f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_forwarder_with_seed, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_with_seed(42, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers with passthrough alias lets",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_if_branches_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_if(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  if flag\n    f(x)\n  else\n    f(x)\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_if(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-if-branches",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept branch-exclusive higher-order wrappers when both branches forward the same unique handoff",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_if_branches_exit_code() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-module-alias-if-branches");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_if(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  if flag\n    f(x)\n  else\n    f(x)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
            &source_path,
            "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_forwarder_if(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers with equivalent branch handoff bodies",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_block_alias_then_if_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_block_if(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  if flag\n    f(y)\n  else\n    f(y)\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_block_if(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-block-alias-then-if",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers that alias the unique root before a branch-equivalent forward handoff",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_block_alias_then_if_exit_code()
{
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-module-alias-block-alias-then-if",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_block_if(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  if flag\n    f(y)\n  else\n    f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
            &source_path,
            "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_forwarder_block_if(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers that alias the unique root before equivalent branch handoff",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_if_passthrough_branch_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_or_passthrough(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  if flag\n    f(x)\n  else\n    x\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_or_passthrough(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-if-passthrough-branch",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers where one branch forwards and the other safely passthroughs the unique value",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_if_passthrough_branch_exit_code(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-module-alias-if-passthrough-branch",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_or_passthrough(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  if flag\n    f(x)\n  else\n    x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
            &source_path,
            "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_forwarder_or_passthrough(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers with forward-or-passthrough branch shapes",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_if_nested_passthrough_alias_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_or_nested_passthrough(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  if flag\n    f(x)\n  else\n    let out = if inner\n      x\n    else\n      x\n    out\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_or_nested_passthrough(true, false, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-if-nested-passthrough-alias",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers where passthrough branches use nested alias-return blocks",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_if_nested_passthrough_alias_exit_code(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-module-alias-if-nested-passthrough-alias",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_or_nested_passthrough(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  if flag\n    f(x)\n  else\n    let out = if inner\n      x\n    else\n      x\n    out\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
            &source_path,
            "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_forwarder_or_nested_passthrough(true, false, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers with nested passthrough alias branches",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_if_branches_exit_code() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-if-branches");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_if(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  if flag\n    f(x)\n  else\n    f(x)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_forwarder_if, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_if(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers with equivalent branch handoff bodies",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_block_alias_then_if_exit_code()
{
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-block-alias-then-if");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_block_if(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  if flag\n    f(y)\n  else\n    f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_forwarder_block_if, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_block_if(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers that alias the unique root before equivalent branch handoff",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_if_passthrough_branch_exit_code()
{
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-if-passthrough-branch");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_or_passthrough(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  if flag\n    f(x)\n  else\n    x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_forwarder_or_passthrough, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_or_passthrough(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers with forward-or-passthrough branch shapes",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_if_nested_passthrough_alias_exit_code(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-if-nested-passthrough-alias",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_or_nested_passthrough(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  if flag\n    f(x)\n  else\n    let out = if inner\n      x\n    else\n      x\n    out\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_forwarder_or_nested_passthrough, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_or_nested_passthrough(true, false, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers with nested passthrough alias branches",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_named_import_call_exit_code() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-forwarder-imported");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
            src_dir.join("wrappers.kea"),
            "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  f(x)\n",
        )
        .expect("wrappers module write should succeed");
    std::fs::write(
            &source_path,
            "use Wrappers.{apply_forwarder, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder(forward_once, x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path).expect(
            "@fip verifier should accept named-import higher-order forwarder calls with known-safe function items",
        );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_call_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-wrapper");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  f(x)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_forwarder, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder(forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier should accept named-import higher-order wrapper calls with known-safe function items",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_alias_chain_call_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  f(y)\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_alias(forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-alias-chain",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept higher-order wrappers that only alias the unique value before forwarding",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_function_alias_chain_call_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = f\n  let y = x\n  g(y)\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_alias(forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-fn-alias-chain",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept higher-order wrappers that alias the forwarder function parameter before single forwarding",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_tuple_alias_chain() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_tuple_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let (g, y) = (f, x)\n  g(y)\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_tuple_alias(forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-tuple-alias-chain",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject tuple-pattern wrapper boundaries until tuple-let lowering is allocation-free",
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary failure, got: {err}"
    );
    assert!(
        err.contains("apply_tuple_alias"),
        "expected tuple-wrapper call site in diagnostics, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_result_alias_chain_call_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias_result(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  let z = y\n  let out0 = f(z)\n  let out1 = out0\n  out1\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_alias_result(forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-result-alias-chain",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept higher-order wrappers that alias the unique input and return through result aliases after a single forward call",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_result_if_alias_chain_call_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_result_if_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let out1 = if flag\n    out0\n  else\n    out0\n  let out2 = out1\n  out2\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_result_if_alias(forward_once, x, true)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-result-if-alias-chain",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept higher-order wrappers that perform call-free if-selection over forwarded result aliases",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_combo_alias_prelude_and_result_if_exit_code(
) {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo(flag_f: Bool, flag_x: Bool, seed: Int, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed2 = if seed > 0\n    seed\n  else\n    seed\n  let g = if flag_f\n    f\n  else\n    f\n  let y = if flag_x\n    x\n  else\n    x\n  let out0 = g(y)\n  let out1 = if flag_f\n    out0\n  else\n    out0\n  let out2 = out1\n  out2\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo(true, false, 42, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-combo-alias",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers that combine pre-forward alias selection with post-forward result-if alias shaping",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_combo_alias_with_benign_let_and_result_if_exit_code(
) {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_plus(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = 42\n  let g = if flag\n    f\n  else\n    f\n  let y = if flag\n    x\n  else\n    x\n  let out0 = g(y)\n  let keep = seed\n  let out1 = if flag\n    out0\n  else\n    out0\n  let out2 = out1\n  out2\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_plus(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-combo-plus-alias",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers that combine benign call-free prelude/result lets with alias-preserving forward/result-if shaping",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_combo_case_alias_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_case(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = case flag\n    true ->\n      f\n    false ->\n      f\n  let y = case flag\n    true ->\n      x\n    false ->\n      x\n  let out0 = g(y)\n  let out1 = case flag\n    true ->\n      out0\n    false ->\n      out0\n  out1\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_case(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-combo-case-alias",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers that use case-based alias selection and result shaping around a single forward handoff",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_combo_case_with_benign_let_and_result_case_exit_code(
) {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_case_plus(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = if flag\n    1\n  else\n    2\n  let g = case flag\n    true ->\n      f\n    false ->\n      f\n  let y = case flag\n    true ->\n      x\n    false ->\n      x\n  let out0 = g(y)\n  let keep = seed\n  let out1 = case flag\n    true ->\n      out0\n    false ->\n      out0\n  let out2 = out1\n  out2\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_case_plus(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-combo-case-plus-alias",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers combining case-based alias shaping with benign call-free prelude/result lets",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_combo_mixed_if_case_with_benign_lets_exit_code(
) {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_mixed(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = if flag\n    7\n  else\n    8\n  let g = case flag\n    true ->\n      if inner\n        f\n      else\n        f\n    false ->\n      f\n  let y = if flag\n    case inner\n      true ->\n        x\n      false ->\n        x\n  else\n    x\n  let out0 = g(y)\n  let keep = seed\n  let out1 = if inner\n    case flag\n      true ->\n        out0\n      false ->\n        out0\n  else\n    out0\n  let out2 = out1\n  out2\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_mixed(true, false, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-combo-mixed-if-case-benign",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers that combine nested call-free if/case alias shaping with benign prelude/result lets",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_combo_mixed_if_case_with_benign_lets_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-combo-mixed-if-case");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_mixed(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = if flag\n    7\n  else\n    8\n  let g = case flag\n    true ->\n      if inner\n        f\n      else\n        f\n    false ->\n      f\n  let y = if flag\n    case inner\n      true ->\n        x\n      false ->\n        x\n  else\n    x\n  let out0 = g(y)\n  let keep = seed\n  let out1 = if inner\n    case flag\n      true ->\n        out0\n      false ->\n        out0\n  else\n    out0\n  let out2 = out1\n  out2\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_combo_mixed(true, false, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers combining nested call-free if/case alias shaping with benign lets",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_combo_mixed_if_case_with_benign_lets_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-combo-mixed-if-case");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_mixed(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = if flag\n    7\n  else\n    8\n  let g = case flag\n    true ->\n      if inner\n        f\n      else\n        f\n    false ->\n      f\n  let y = if flag\n    case inner\n      true ->\n        x\n      false ->\n        x\n  else\n    x\n  let out0 = g(y)\n  let keep = seed\n  let out1 = if inner\n    case flag\n      true ->\n        out0\n      false ->\n        out0\n  else\n    out0\n  let out2 = out1\n  out2\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_combo_mixed, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_mixed(true, false, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers combining nested call-free if/case alias shaping with benign lets",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_result_alias_with_benign_noncall_let_exit_code(
) {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_result_with_benign_let(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let keep = if flag\n    1\n  else\n    2\n  let out1 = out0\n  out1\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_result_with_benign_let(forward_once, x, true)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-result-benign-let",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers with benign call-free non-alias lets after a single forward handoff",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_with_benign_noncall_prelude_let_exit_code(
) {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_with_prelude_setup(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = if flag\n    1\n  else\n    2\n  let y = x\n  let out = f(y)\n  out\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_with_prelude_setup(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-benign-prelude-let",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers with benign call-free prelude lets before forwarding",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_with_if_selected_unique_alias_exit_code() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_pick_unique(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = if flag\n    x\n  else\n    x\n  f(y)\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_pick_unique(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-if-selected-unique-alias",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers that select the unique handoff alias through a call-free if",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_with_if_selected_forwarder_alias_exit_code(
) {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_pick_forwarder(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = if flag\n    f\n  else\n    f\n  g(x)\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_pick_forwarder(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-if-selected-forwarder-alias",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers that select the forwarder alias through a call-free if",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_param_escape() {
    let source_path = write_temp_source(
        "fn apply_forwarder(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  f(x)\n\n@fip\nfn call_via_apply(x: Unique Int, f: fn(Unique Int) -> Unique Int) -> Unique Int\n  apply_forwarder(f, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-param-escape",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
            "@fip verifier should reject higher-order forwarding when the forwarded callee is unresolved at call boundary",
        );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected call-boundary escape diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_wrong_unique_arg_escape() {
        let source_path = write_temp_source(
            "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_wrong(f: fn(Unique Int) -> Unique Int, x: Unique Int, y: Unique Int) -> Unique Int\n  f(y)\n\n@fip\nfn call_via_apply(x: Unique Int, y: Unique Int) -> Unique Int\n  apply_wrong(forward_once, x, y)\n\nfn main() -> Int\n  0\n",
            "kea-cli-fip-unique-higher-order-forwarder-wrong-arg-escape",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
            "@fip verifier should reject higher-order wrappers when the tracked unique parameter is not the forwarded argument",
        );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

        let _ = std::fs::remove_file(source_path);
    }

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_wrong_unique_arg_escape() {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-wrong-arg-escape",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_wrong(f: fn(Unique Int) -> Unique Int, x: Unique Int, y: Unique Int) -> Unique Int\n  f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int, y: Unique Int) -> Unique Int\n  A.apply_wrong(A.forward_once, x, y)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject module-alias wrappers when the tracked unique parameter is not the forwarded argument",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_wrong_unique_arg_escape() {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-wrong-arg-escape",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_wrong(f: fn(Unique Int) -> Unique Int, x: Unique Int, y: Unique Int) -> Unique Int\n  f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_wrong, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int, y: Unique Int) -> Unique Int\n  apply_wrong(forward_once, x, y)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject named-import wrappers when the tracked unique parameter is not the forwarded argument",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_rejects_fip_unique_higher_order_wrapper_when_safe_forwarder_is_not_body_slot() {
        let source_path = write_temp_source(
            "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_pick_first(f: fn(Unique Int) -> Unique Int, g: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  f(x)\n\n@fip\nfn call_via_apply(x: Unique Int, f: fn(Unique Int) -> Unique Int) -> Unique Int\n  apply_pick_first(f, forward_once, x)\n\nfn main() -> Int\n  0\n",
            "kea-cli-fip-unique-higher-order-forwarder-nonbody-slot",
            "kea",
        );

        let err = run_file(&source_path).expect_err(
            "@fip verifier should reject when the known-safe function item is not passed in the wrapper's body-selected forwarder slot",
        );
        assert!(
            err.contains("`@fip` verification failed for `call_via_apply`"),
            "expected @fip verification failure, got: {err}"
        );
        assert!(
            err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
            "expected escape diagnostic for `x`, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn compile_rejects_fip_unique_higher_order_function_alias_wrapper_when_safe_forwarder_is_not_body_slot() {
        let source_path = write_temp_source(
            "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_pick_alias(f: fn(Unique Int) -> Unique Int, g: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let h = f\n  h(x)\n\n@fip\nfn call_via_apply(x: Unique Int, f: fn(Unique Int) -> Unique Int) -> Unique Int\n  apply_pick_alias(f, forward_once, x)\n\nfn main() -> Int\n  0\n",
            "kea-cli-fip-unique-higher-order-forwarder-fn-alias-wrong-slot",
            "kea",
        );

        let err = run_file(&source_path).expect_err(
            "@fip verifier should reject when a known-safe function item is passed outside the body-selected forwarder slot, even with forwarder-param aliasing",
        );
        assert!(
            err.contains("`@fip` verification failed for `call_via_apply`"),
            "expected @fip verification failure, got: {err}"
        );
        assert!(
            err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
            "expected escape diagnostic for `x`, got: {err}"
        );

        let _ = std::fs::remove_file(source_path);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_call_exit_code() {
        let project_dir =
            temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-wrapper");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");
        let source_path = src_dir.join("main.kea");
        std::fs::write(
            src_dir.join("alpha.kea"),
            "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  f(x)\n",
        )
        .expect("alpha module write should succeed");
        std::fs::write(
            &source_path,
            "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_forwarder(A.forward_once, x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

        let run = run_file(&source_path).expect(
            "@fip verifier and backend lowering should accept higher-order module-alias wrapper calls",
        );
        assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_tuple_alias_chain()
{
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-wrapper-tuple-alias");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_tuple_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let (g, y) = (f, x)\n  g(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_tuple_alias(A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject module-alias tuple-pattern wrapper boundaries until tuple-let lowering is allocation-free",
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary failure, got: {err}"
    );
    assert!(
        err.contains("A.apply_tuple_alias"),
        "expected tuple-wrapper module-alias call site in diagnostics, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_tuple_alias_chain() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-wrapper-tuple-alias");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_tuple_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let (g, y) = (f, x)\n  g(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_tuple_alias, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_tuple_alias(forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject named-import tuple-pattern wrapper boundaries until tuple-let lowering is allocation-free",
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary failure, got: {err}"
    );
    assert!(
        err.contains("apply_tuple_alias"),
        "expected tuple-wrapper named-import call site in diagnostics, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_param_escape() {
        let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-param");
        let src_dir = project_dir.join("src");
        std::fs::create_dir_all(&src_dir).expect("source dir should be created");
        let source_path = src_dir.join("main.kea");
        std::fs::write(
            src_dir.join("alpha.kea"),
            "fn apply_forwarder(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  f(x)\n",
        )
        .expect("alpha module write should succeed");
        std::fs::write(
            &source_path,
            "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int, f: fn(Unique Int) -> Unique Int) -> Unique Int\n  A.apply_forwarder(f, x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

        let err = run_file(&source_path).expect_err(
            "@fip verifier should reject higher-order alias wrapper calls when forwarded callee remains unresolved at call boundary",
        );
        assert!(
            err.contains("`@fip` verification failed for `call_via_apply`"),
            "expected @fip verification failure, got: {err}"
        );
        assert!(
            err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
            "expected escape diagnostic for `x`, got: {err}"
        );
        assert!(
            !err.contains("unresolved qualified call target `A.apply_forwarder`"),
            "expected @fip rejection before codegen alias-gap diagnostics, got: {err}"
        );

        let _ = std::fs::remove_dir_all(project_dir);
    }

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_param_escape() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-param");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn apply_forwarder(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  f(x)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_forwarder}\n\n@fip\nfn call_via_apply(x: Unique Int, f: fn(Unique Int) -> Unique Int) -> Unique Int\n  apply_forwarder(f, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject higher-order named-import wrapper calls when forwarded callee remains unresolved at call boundary",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_known_qualified_forwarder_call_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-qualified-forwarder");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
            &source_path,
            "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_forward_once(x: Unique Int) -> Unique Int\n  Main.forward_once(x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path)
        .expect("@fip verifier should accept qualified known safe forwarder calls");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_alias_chain_call_exit_code() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-alias-chain");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_alias(A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers that alias the unique value before forwarding",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_alias_chain_call_exit_code() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-alias-chain");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_alias, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_alias(forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers that alias the unique value before forwarding",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_function_alias_chain_call_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-fn-alias-chain");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = f\n  let y = x\n  g(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_forwarder_alias(A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers that alias the forwarder parameter before single forwarding",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_function_alias_chain_call_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-fn-alias-chain");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_forwarder_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = f\n  let y = x\n  g(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_forwarder_alias, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_forwarder_alias(forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers that alias the forwarder parameter before single forwarding",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_result_alias_chain_call_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-result-alias");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias_result(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  let z = y\n  let out0 = f(z)\n  let out1 = out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_alias_result(A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers that return through result aliases after a single forward call",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_result_alias_chain_call_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-result-alias");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias_result(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  let z = y\n  let out0 = f(z)\n  let out1 = out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_alias_result, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_alias_result(forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers that return through result aliases after a single forward call",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_result_if_alias_chain_call_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-result-if-alias");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_result_if_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let out1 = if flag\n    out0\n  else\n    out0\n  let out2 = out1\n  out2\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_result_if_alias(A.forward_once, x, true)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers with call-free result-if alias selection",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_result_alias_with_benign_noncall_let_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-result-benign-let");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_result_with_benign_let(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let keep = if flag\n    1\n  else\n    2\n  let out1 = out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_result_with_benign_let(A.forward_once, x, true)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers with benign call-free non-alias lets after forwarding",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_with_benign_noncall_prelude_let_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-benign-prelude-let");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_with_prelude_setup(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = if flag\n    1\n  else\n    2\n  let y = x\n  let out = f(y)\n  out\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_with_prelude_setup(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers with benign call-free prelude lets",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_result_if_alias_chain_call_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-result-if-alias");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_result_if_alias(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let out1 = if flag\n    out0\n  else\n    out0\n  let out2 = out1\n  out2\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_result_if_alias, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_result_if_alias(forward_once, x, true)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers with call-free result-if alias selection",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_result_alias_with_benign_noncall_let_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-result-benign-let");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_result_with_benign_let(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let keep = if flag\n    1\n  else\n    2\n  let out1 = out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_result_with_benign_let, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_result_with_benign_let(forward_once, x, true)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers with benign call-free non-alias lets after forwarding",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_with_benign_noncall_prelude_let_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-benign-prelude-let");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_with_prelude_setup(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = if flag\n    1\n  else\n    2\n  let y = x\n  let out = f(y)\n  out\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_with_prelude_setup, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_with_prelude_setup(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers with benign call-free prelude lets",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_with_if_selected_unique_alias_exit_code(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-if-selected-unique-alias",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_pick_unique(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = if flag\n    x\n  else\n    x\n  f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_pick_unique(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers with if-selected unique aliases",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_with_if_selected_forwarder_alias_exit_code(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-if-selected-forwarder-alias",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_pick_forwarder(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = if flag\n    f\n  else\n    f\n  g(x)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_pick_forwarder(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers with if-selected forwarder aliases",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_with_if_selected_unique_alias_exit_code(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-if-selected-unique-alias",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_pick_unique(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = if flag\n    x\n  else\n    x\n  f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_pick_unique, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_pick_unique(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers with if-selected unique aliases",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_with_if_selected_forwarder_alias_exit_code(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-if-selected-forwarder-alias",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_pick_forwarder(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = if flag\n    f\n  else\n    f\n  g(x)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_pick_forwarder, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_pick_forwarder(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers with if-selected forwarder aliases",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_combo_alias_with_benign_let_and_result_if_exit_code(
) {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-combo-plus");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_plus(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = 42\n  let g = if flag\n    f\n  else\n    f\n  let y = if flag\n    x\n  else\n    x\n  let out0 = g(y)\n  let keep = seed\n  let out1 = if flag\n    out0\n  else\n    out0\n  let out2 = out1\n  out2\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_combo_plus(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers that combine benign call-free lets with alias-preserving forward/result-if shaping",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_combo_case_alias_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-combo-case");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_case(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = case flag\n    true ->\n      f\n    false ->\n      f\n  let y = case flag\n    true ->\n      x\n    false ->\n      x\n  let out0 = g(y)\n  let out1 = case flag\n    true ->\n      out0\n    false ->\n      out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_combo_case(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers that use case-based alias selection and result shaping around a single forward handoff",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_combo_case_with_benign_let_and_result_case_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-combo-case-plus");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_case_plus(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = if flag\n    1\n  else\n    2\n  let g = case flag\n    true ->\n      f\n    false ->\n      f\n  let y = case flag\n    true ->\n      x\n    false ->\n      x\n  let out0 = g(y)\n  let keep = seed\n  let out1 = case flag\n    true ->\n      out0\n    false ->\n      out0\n  let out2 = out1\n  out2\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_combo_case_plus(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers combining case-based alias shaping with benign call-free lets",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_combo_alias_with_benign_let_and_result_if_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-combo-plus");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_plus(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = 42\n  let g = if flag\n    f\n  else\n    f\n  let y = if flag\n    x\n  else\n    x\n  let out0 = g(y)\n  let keep = seed\n  let out1 = if flag\n    out0\n  else\n    out0\n  let out2 = out1\n  out2\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_combo_plus, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_plus(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers that combine benign call-free lets with alias-preserving forward/result-if shaping",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_combo_case_alias_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-combo-case");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_case(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = case flag\n    true ->\n      f\n    false ->\n      f\n  let y = case flag\n    true ->\n      x\n    false ->\n      x\n  let out0 = g(y)\n  let out1 = case flag\n    true ->\n      out0\n    false ->\n      out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_combo_case, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_case(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers that use case-based alias selection and result shaping around a single forward handoff",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_combo_case_with_benign_let_and_result_case_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-combo-case-plus");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo_case_plus(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = if flag\n    1\n  else\n    2\n  let g = case flag\n    true ->\n      f\n    false ->\n      f\n  let y = case flag\n    true ->\n      x\n    false ->\n      x\n  let out0 = g(y)\n  let keep = seed\n  let out1 = case flag\n    true ->\n      out0\n    false ->\n      out0\n  let out2 = out1\n  out2\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_combo_case_plus, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_case_plus(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers combining case-based alias shaping with benign call-free lets",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_forwarder_mixed_result_and_passthrough_if_exit_code()
{
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_mixed(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let out = if flag\n    let r0 = f(x)\n    let r1 = if inner\n      r0\n    else\n      r0\n    r1\n  else\n    let p0 = if inner\n      x\n    else\n      x\n    let p1 = p0\n    p1\n  let ret = out\n  ret\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_mixed(true, false, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-mixed-result-passthrough-if",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept wrappers that combine forwarded-result alias shaping with passthrough fallback branches",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_mixed_result_and_passthrough_if_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-mixed-result-pass");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_mixed(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let out = if flag\n    let r0 = f(x)\n    let r1 = if inner\n      r0\n    else\n      r0\n    r1\n  else\n    let p0 = if inner\n      x\n    else\n      x\n    let p1 = p0\n    p1\n  let ret = out\n  ret\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_mixed(true, false, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers that mix forwarded-result and passthrough branch forms",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_mixed_result_and_passthrough_if_exit_code(
) {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-mixed-result-pass");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_mixed(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let out = if flag\n    let r0 = f(x)\n    let r1 = if inner\n      r0\n    else\n      r0\n    r1\n  else\n    let p0 = if inner\n      x\n    else\n      x\n    let p1 = p0\n    p1\n  let ret = out\n  ret\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_mixed, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_mixed(true, false, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers that mix forwarded-result and passthrough branch forms",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_module_alias_wrapper_combo_alias_prelude_and_result_if_exit_code(
) {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-higher-order-alias-combo");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo(flag_f: Bool, flag_x: Bool, seed: Int, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed2 = if seed > 0\n    seed\n  else\n    seed\n  let g = if flag_f\n    f\n  else\n    f\n  let y = if flag_x\n    x\n  else\n    x\n  let out0 = g(y)\n  let out1 = if flag_f\n    out0\n  else\n    out0\n  let out2 = out1\n  out2\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_combo(true, false, 42, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept module-alias wrappers that combine pre-forward alias selection with post-forward result-if alias shaping",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_higher_order_named_import_wrapper_combo_alias_prelude_and_result_if_exit_code(
) {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-higher-order-named-combo");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_combo(flag_f: Bool, flag_x: Bool, seed: Int, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed2 = if seed > 0\n    seed\n  else\n    seed\n  let g = if flag_f\n    f\n  else\n    f\n  let y = if flag_x\n    x\n  else\n    x\n  let out0 = g(y)\n  let out1 = if flag_f\n    out0\n  else\n    out0\n  let out2 = out1\n  out2\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_combo, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo(true, false, 42, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should accept named-import wrappers that combine pre-forward alias selection with post-forward result-if alias shaping",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_qualified_forwarder_with_ambiguous_short_names_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-qualified-ambiguous");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        src_dir.join("beta.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("beta module write should succeed");
    std::fs::write(
            &source_path,
            "use Alpha\nuse Beta\n\n@fip\nfn call_forward_once(x: Unique Int) -> Unique Int\n  Alpha.forward_once(x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier should accept qualified safe forwarder calls when short names are ambiguous",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_named_import_forwarder_call_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-named-import-forwarder");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
            &source_path,
            "use Alpha.{forward_once}\n\n@fip\nfn call_forward_once(x: Unique Int) -> Unique Int\n  forward_once(x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path)
        .expect("@fip verifier should accept named-import safe forwarder calls");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_module_alias_forwarder_call_exit_code() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-module-alias-forwarder");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
            &source_path,
            "use Alpha as A\n\n@fip\nfn call_forward_once(x: Unique Int) -> Unique Int\n  A.forward_once(x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path)
        .expect("@fip verifier and backend lowering should accept module-alias qualified calls");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_module_alias_forwarder_call_ignores_local_operation_shadowing() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-alias-opname-shadowed-param");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
            &source_path,
            "use Alpha as A\n\n@fip\nfn call_forward_once(x: Unique Int, forward_once: fn(Unique Int) -> Unique Int) -> Unique Int\n  A.forward_once(x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let run = run_file(&source_path).expect(
        "@fip verifier and backend lowering should resolve module-alias qualified names even when local params shadow operation names",
    );
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_let_shadow_escape() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-named-import-let-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\n@fip\nfn call_via_named_import_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  let forward_once = g\n  forward_once(x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through let-shadowing of a named-imported safe forwarder",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary signal for named-import shadow path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_param_shadow_escape() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-named-import-param-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\n@fip\nfn call_via_named_import_param_shadow(x: Unique Int, forward_once: fn(Unique Int) -> Unique Int) -> Unique Int\n  forward_once(x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through parameter shadowing of a named-imported safe forwarder",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_param_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary signal for named-import param shadow path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_case_pattern_shadow_escape() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-named-import-case-pattern-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\n@fip\nfn call_via_named_import_case_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  case Some(g)\n    Some(forward_once) ->\n      forward_once(x)\n    None ->\n      x\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through case-pattern shadowing of a named-imported safe forwarder",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_case_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary signal for named-import case-pattern shadow path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_lambda_shadow_escape() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-named-import-lambda-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\n@fip\nfn call_via_named_import_lambda_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  (|forward_once| forward_once(x))(g)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through lambda shadowing of a named-imported safe forwarder",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_lambda_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary signal for named-import lambda shadow path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_if_shadow_escape() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-named-import-if-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\n@fip\nfn call_via_named_import_if_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  if true\n    let forward_once = g\n    forward_once(x)\n  else\n    x\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through if-branch shadowing of a named-imported safe forwarder",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_if_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary signal for named-import if-shadow path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_pattern_shadow_escape() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-named-import-pattern-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\n@fip\nfn call_via_named_import_pattern_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  let (forward_once, y) = (g, x)\n  forward_once(y)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through named-import pattern shadow",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_pattern_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary signal for named-import pattern-shadow path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_case_let_shadow_escape() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-named-import-case-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\n@fip\nfn call_via_named_import_case_let_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  case true\n    true ->\n      let forward_once = g\n      forward_once(x)\n    false ->\n      x\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through named-import case-arm let shadow",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_case_let_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary signal for named-import case-let-shadow path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_handle_clause_shadow_escape() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-named-import-forwarder-handle-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\neffect Wrap C\n  fn op(v: C, forward_once: fn(C) -> C) -> C\n\n@fip\nfn call_via_named_import_handle_shadow(x: Unique Int) -> Unique Int\n  handle x\n    Wrap.op(v, forward_once) -> resume forward_once(v)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through named-import handle-clause shadow",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_handle_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary signal for named-import handle-clause shadow path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_then_shadow_escape() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-named-import-forwarder-then-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\neffect Dummy\n  fn noop() -> Unit\n\n@fip\nfn call_via_named_import_then_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  handle g\n    Dummy.noop() -> resume ()\n    then forward_once -> forward_once(x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through named-import then-lambda shadow",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_then_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unresolved call-boundary signal for named-import then-lambda shadow path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_with_shadow_escape() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-named-import-forwarder-with-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\nfn with_forwarder(f: fn(Unique Int) -> Unique Int, @with k: fn(fn(Unique Int) -> Unique Int) -> Unique Int) -> Unique Int\n  k(f)\n\n@fip\nfn call_via_named_import_with_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  with forward_once <- with_forwarder(g)\n  forward_once(x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through named-import with-binding shadow",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_with_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=2"),
        "expected unresolved call-boundary count for with-forwarder + named-import with-shadow path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_handle_clause_no_shadow_without_boundary_escape() {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-named-import-forwarder-handle-no-shadow",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\neffect Wrap C\n  fn op(v: C, cb: fn(C) -> C) -> C\n\n@fip\nfn call_via_named_import_handle_no_shadow(x: Unique Int) -> Unique Int\n  handle x\n    Wrap.op(v, cb) -> resume forward_once(v)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should still fail this shape for non-boundary reasons, but must not report unsupported call boundaries for unshadowed named import",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_handle_no_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        !err.contains("unsupported_call_boundaries="),
        "expected no unresolved call-boundary diagnostics for unshadowed named-import handle path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_then_no_shadow_without_boundary_escape() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-named-import-forwarder-then-no-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\neffect Dummy\n  fn noop() -> Unit\n\n@fip\nfn call_via_named_import_then_no_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  handle g\n    Dummy.noop() -> resume ()\n    then f -> forward_once(x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should still fail this shape for non-boundary reasons, but must not report unsupported call boundaries for unshadowed named import",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_then_no_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        !err.contains("unsupported_call_boundaries="),
        "expected no unresolved call-boundary diagnostics for unshadowed named-import then path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_named_import_forwarder_with_no_shadow_without_local_boundary_escape() {
    let project_dir =
        temp_workspace_project_dir("kea-cli-fip-unique-named-import-forwarder-with-no-shadow");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\nfn with_forwarder(f: fn(Unique Int) -> Unique Int, @with k: fn(fn(Unique Int) -> Unique Int) -> Unique Int) -> Unique Int\n  k(f)\n\n@fip\nfn call_via_named_import_with_no_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  with fwd <- with_forwarder(g)\n  forward_once(x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should still fail for with-forwarder boundary, but must not report a local shadow boundary for unshadowed named import",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_named_import_with_no_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected only the with-forwarder unresolved boundary, got: {err}"
    );
    assert!(
        !err.contains("forward_once$m0$Dyn"),
        "expected no local shadow callable boundary site for unshadowed named-import with path, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_module_alias_forwarder_case_pattern_unshadowed_exit_code() {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-module-alias-forwarder-case-pattern-unshadowed",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\nenum Wrap a\n  Wrap(a)\n\n@fip\nfn call_via_module_alias_case_pattern_no_shadow(x: Unique Int, w: Wrap(fn(Unique Int) -> Unique Int)) -> Unique Int\n  case w\n    Wrap(cb) ->\n      A.forward_once(x)\n\nfn main() -> Int\n  let w = Wrap(A.forward_once)\n  call_via_module_alias_case_pattern_no_shadow(7, w)\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path)
        .expect("module-alias case-pattern no-shadow path should compile and execute");
    assert_eq!(run.exit_code, 7);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_named_import_forwarder_case_pattern_unshadowed_exit_code() {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-named-import-forwarder-case-pattern-unshadowed",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n",
    )
    .expect("alpha module write should succeed");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        &source_path,
        "use Alpha.{forward_once}\n\nenum Wrap a\n  Wrap(a)\n\n@fip\nfn call_via_named_import_case_pattern_no_shadow(x: Unique Int, w: Wrap(fn(Unique Int) -> Unique Int)) -> Unique Int\n  case w\n    Wrap(cb) ->\n      forward_once(x)\n\nfn main() -> Int\n  let w = Wrap(forward_once)\n  call_via_named_import_case_pattern_no_shadow(7, w)\n",
    )
    .expect("source write should succeed");

    let run = run_file(&source_path)
        .expect("named-import case-pattern no-shadow path should compile and execute");
    assert_eq!(run.exit_code, 7);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_shadowed_forwarder_name_call_escape() {
    let project_dir = temp_workspace_project_dir("kea-cli-fip-unique-shadowed-forwarder-name");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
            &source_path,
            "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_param(x: Unique Int, forward_once: fn(Unique Int) -> Unique Int) -> Unique Int\n  forward_once(x)\n\nfn main() -> Int\n  0\n",
        )
        .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through shadowed forwarder name",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_param`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported cross-function call boundaries (1):"),
        "expected call-boundary escape diagnostic, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_let_shadowed_forwarder_name_call_escape() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_let_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  let forward_once = g\n  forward_once(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-let-shadowed-forwarder-name",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through let-shadowed forwarder name",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_let_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("escapes through 1 call argument(s)"),
        "expected call-boundary escape diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_pattern_shadowed_forwarder_name_call_escape() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_pattern_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  let (forward_once, y) = (g, x)\n  forward_once(y)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-pattern-shadowed-forwarder-name",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through destructuring-shadowed forwarder name",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_pattern_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected call-boundary escape diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_lambda_shadowed_forwarder_name_call_escape() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_lambda_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  (|forward_once| forward_once(x))(g)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-lambda-shadowed-forwarder-name",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through lambda-shadowed forwarder name",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_lambda_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported cross-function call boundaries (1):"),
        "expected call-boundary escape diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_case_shadowed_forwarder_name_call_escape() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_case_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  case true\n    true ->\n      let forward_once = g\n      forward_once(x)\n    false ->\n      x\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-case-shadowed-forwarder-name",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through case-arm-shadowed forwarder name",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_case_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported cross-function call boundaries (1):"),
        "expected call-boundary escape diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_if_shadowed_forwarder_name_call_escape() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_if_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  if true\n    let forward_once = g\n    forward_once(x)\n  else\n    x\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-if-shadowed-forwarder-name",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through if-branch-shadowed forwarder name",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_if_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported cross-function call boundaries (1):"),
        "expected call-boundary escape diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_handle_clause_shadowed_forwarder_name_call_escape() {
    let source_path = write_temp_source(
        "effect Wrap C\n  fn op(v: C, forward_once: fn(C) -> C) -> C\n\nfn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_handle_clause_shadow(x: Unique Int) -> Unique Int\n  handle x\n    Wrap.op(v, forward_once) -> resume forward_once(v)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-handle-clause-shadowed-forwarder-name",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through handle-clause-shadowed forwarder name",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_handle_clause_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported cross-function call boundaries (1):"),
        "expected call-boundary escape diagnostic, got: {err}"
    );
    assert!(
        err.contains("- forward_once"),
        "expected local callable site in diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_handle_clause_unshadowed_forwarder_without_boundary_escape() {
    let source_path = write_temp_source(
        "effect Wrap C\n  fn op(v: C, cb: fn(C) -> C) -> C\n\nfn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_handle_clause_no_shadow(x: Unique Int) -> Unique Int\n  handle x\n    Wrap.op(v, cb) -> resume forward_once(v)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-handle-clause-unshadowed-forwarder",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should still fail this shape for non-boundary reasons (release), but must not report unsupported call boundaries",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_handle_clause_no_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        !err.contains("unsupported cross-function call boundaries"),
        "expected no unsupported call-boundary diagnostics for unshadowed global forwarder call, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_then_lambda_shadowed_forwarder_name_call_escape() {
    let source_path = write_temp_source(
        "effect Dummy\n  fn noop() -> Unit\n\nfn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_then_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  handle g\n    Dummy.noop() -> resume ()\n    then forward_once -> forward_once(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-then-shadowed-forwarder-name",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through then-lambda-shadowed forwarder name",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_then_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported cross-function call boundaries (1):"),
        "expected call-boundary escape diagnostic, got: {err}"
    );
    assert!(
        err.contains("- forward_once"),
        "expected local callable site in diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_then_lambda_unshadowed_forwarder_without_boundary_escape() {
    let source_path = write_temp_source(
        "effect Dummy\n  fn noop() -> Unit\n\nfn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_then_no_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  handle g\n    Dummy.noop() -> resume ()\n    then f -> forward_once(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-then-unshadowed-forwarder",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should still fail this shape for non-boundary reasons (release), but must not report unsupported call boundaries",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_then_no_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        !err.contains("unsupported cross-function call boundaries"),
        "expected no unsupported call-boundary diagnostics for unshadowed then-lambda global forwarder call, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_with_binding_shadowed_forwarder_name_call_escape() {
    let source_path = write_temp_source(
        "fn with_forwarder(f: fn(Unique Int) -> Unique Int, @with k: fn(fn(Unique Int) -> Unique Int) -> Unique Int) -> Unique Int\n  k(f)\n\nfn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_with_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  with forward_once <- with_forwarder(g)\n  forward_once(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-with-shadowed-forwarder-name",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through with-binding-shadowed forwarder name",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_with_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported cross-function call boundaries (2):"),
        "expected two unsupported boundaries (`with_forwarder` and shadowed local callable), got: {err}"
    );
    assert!(
        err.contains("- forward_once"),
        "expected local callable site from with-binding shadow, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_with_binding_unshadowed_forwarder_without_local_boundary_escape() {
    let source_path = write_temp_source(
        "fn with_forwarder(f: fn(Unique Int) -> Unique Int, @with k: fn(fn(Unique Int) -> Unique Int) -> Unique Int) -> Unique Int\n  k(f)\n\nfn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_with_no_shadow(x: Unique Int, g: fn(Unique Int) -> Unique Int) -> Unique Int\n  with fwd <- with_forwarder(g)\n  forward_once(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-with-unshadowed-forwarder",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should still fail this shape for non-boundary reasons, but must not report shadowed local callable boundaries",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_with_no_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported cross-function call boundaries (1):"),
        "expected only the `with_forwarder` boundary, got: {err}"
    );
    assert!(
        !err.contains("forward_once$m"),
        "expected no local shadow callable boundary in unshadowed with-binding path, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_case_pattern_binder_shadowed_forwarder_name_call_escape() {
    let source_path = write_temp_source(
        "enum Wrap a\n  Wrap(a)\n\nfn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_case_pattern_binder_shadow(x: Unique Int, w: Wrap(fn(Unique Int) -> Unique Int)) -> Unique Int\n  case w\n    Wrap(forward_once) ->\n      forward_once(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-case-pattern-binder-shadowed-forwarder-name",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject call-boundary escape through case-pattern-binder shadowed forwarder name",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_case_pattern_binder_shadow`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries="),
        "expected call-boundary escape diagnostic, got: {err}"
    );
    assert!(
        err.contains("forward_once"),
        "expected local binder callable boundary site naming `forward_once`, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_case_pattern_binder_unshadowed_forwarder_exit_code() {
    let source_path = write_temp_source(
        "enum Wrap a\n  Wrap(a)\n\nfn forward_once(x: Unique Int) -> Unique Int\n  x\n\n@fip\nfn call_via_case_pattern_binder_no_shadow(x: Unique Int, w: Wrap(fn(Unique Int) -> Unique Int)) -> Unique Int\n  case w\n    Wrap(cb) ->\n      forward_once(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-case-pattern-binder-unshadowed-forwarder",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "@fip verifier should accept case-pattern-binder path when forwarder name is not shadowed",
    );
    assert_eq!(run.exit_code, 0, "expected successful execution, got: {run:?}");

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_unique_handoff_missing() {
    let source_path = write_temp_source(
        "@fip\nfn leak(x: Unique Int) -> Int\n  1\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-missing-handoff",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("@fip verifier should reject missing unique handoff");
    assert!(
        err.contains("`@fip` verification failed for `leak`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("never referenced in function body"),
        "expected unique ownership-flow detail, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_alias_chain_with_extra_call() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias_with_extra_call(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  forward_once(y)\n  f(y)\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_alias_with_extra_call(forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-alias-chain-extra-call",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject wrappers that do extra calls before forwarding the unique value",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_alias_chain_with_extra_call() {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-alias-chain-extra-call",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias_with_extra_call(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  forward_once(y)\n  f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_alias_with_extra_call(A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject module-alias wrappers that do extra calls before forwarding the unique value",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_alias_chain_with_extra_call() {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-alias-chain-extra-call",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias_with_extra_call(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  forward_once(y)\n  f(y)\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_alias_with_extra_call, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_alias_with_extra_call(forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject named-import wrappers that do extra calls before forwarding the unique value",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_result_alias_chain_with_extra_call() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias_result_with_extra_call(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  let out = f(y)\n  forward_once(out)\n  out\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_alias_result_with_extra_call(forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-result-alias-chain-extra-call",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject wrappers that do extra calls after forwarding and before returning result aliases",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_result_alias_chain_with_extra_call(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-result-alias-chain-extra-call",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias_result_with_extra_call(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  let out = f(y)\n  forward_once(out)\n  out\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_alias_result_with_extra_call(A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject module-alias wrappers that do extra calls after forwarding and before returning result aliases",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_result_alias_chain_with_extra_call(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-result-alias-chain-extra-call",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_alias_result_with_extra_call(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let y = x\n  let out = f(y)\n  forward_once(out)\n  out\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_alias_result_with_extra_call, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_alias_result_with_extra_call(forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject named-import wrappers that do extra calls after forwarding and before returning result aliases",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_result_if_alias_with_callful_condition() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_result_if_alias_with_callful_condition(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let out1 = if bool_id(flag)\n    out0\n  else\n    out0\n  out1\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_result_if_alias_with_callful_condition(forward_once, x, true)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-result-if-alias-callful-condition",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject wrappers when result-if alias selection uses a callful condition",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_result_if_alias_with_callful_condition(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-result-if-callful-condition",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_result_if_alias_with_callful_condition(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let out1 = if bool_id(flag)\n    out0\n  else\n    out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_result_if_alias_with_callful_condition(A.forward_once, x, true)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject module-alias wrappers when result-if alias shaping uses a callful condition",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_result_if_alias_with_callful_condition(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-result-if-callful-condition",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_result_if_alias_with_callful_condition(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let out1 = if bool_id(flag)\n    out0\n  else\n    out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_result_if_alias_with_callful_condition, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_result_if_alias_with_callful_condition(forward_once, x, true)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject named-import wrappers when result-if alias shaping uses a callful condition",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_combo_mixed_with_callful_condition() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_combo_mixed_with_callful_condition(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = case flag\n    true ->\n      if bool_id(inner)\n        f\n      else\n        f\n    false ->\n      f\n  let out = g(x)\n  out\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_mixed_with_callful_condition(true, false, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-combo-mixed-callful-condition",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject mixed wrappers when pre-forward alias shaping uses a callful condition",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_combo_mixed_with_callful_condition(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-combo-mixed-callful-condition",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_combo_mixed_with_callful_condition(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = case flag\n    true ->\n      if bool_id(inner)\n        f\n      else\n        f\n    false ->\n      f\n  let out = g(x)\n  out\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_combo_mixed_with_callful_condition(true, false, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject module-alias mixed wrappers when pre-forward alias shaping uses a callful condition",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_combo_mixed_with_callful_condition(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-combo-mixed-callful-condition",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_combo_mixed_with_callful_condition(flag: Bool, inner: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = case flag\n    true ->\n      if bool_id(inner)\n        f\n      else\n        f\n    false ->\n      f\n  let out = g(x)\n  out\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_combo_mixed_with_callful_condition, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_mixed_with_callful_condition(true, false, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject named-import mixed wrappers when pre-forward alias shaping uses a callful condition",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_combo_case_with_callful_condition() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_combo_case_with_callful_condition(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = case bool_id(flag)\n    true ->\n      f\n    false ->\n      f\n  let y = case flag\n    true ->\n      x\n    false ->\n      x\n  let out0 = g(y)\n  let out1 = case bool_id(flag)\n    true ->\n      out0\n    false ->\n      out0\n  out1\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_case_with_callful_condition(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-combo-case-callful-condition",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject case-based wrappers when selector shaping uses callful conditions",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_combo_case_with_callful_condition(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-combo-case-callful-condition",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_combo_case_with_callful_condition(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = case bool_id(flag)\n    true ->\n      f\n    false ->\n      f\n  let y = case flag\n    true ->\n      x\n    false ->\n      x\n  let out0 = g(y)\n  let out1 = case bool_id(flag)\n    true ->\n      out0\n    false ->\n      out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_combo_case_with_callful_condition(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject module-alias case-based wrappers when selector shaping uses callful conditions",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_combo_case_with_callful_condition(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-combo-case-callful-condition",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_combo_case_with_callful_condition(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let g = case bool_id(flag)\n    true ->\n      f\n    false ->\n      f\n  let y = case flag\n    true ->\n      x\n    false ->\n      x\n  let out0 = g(y)\n  let out1 = case bool_id(flag)\n    true ->\n      out0\n    false ->\n      out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_combo_case_with_callful_condition, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_case_with_callful_condition(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject named-import case-based wrappers when selector shaping uses callful conditions",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_result_alias_with_callful_nonalias_let() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_result_with_callful_nonalias_let(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let keep = bool_id(flag)\n  let out1 = out0\n  out1\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_result_with_callful_nonalias_let(forward_once, x, true)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-result-callful-nonalias-let",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject wrappers when post-forward non-alias lets contain calls",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_result_alias_with_callful_nonalias_let(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-result-callful-nonalias-let",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_result_with_callful_nonalias_let(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let keep = bool_id(flag)\n  let out1 = out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_result_with_callful_nonalias_let(A.forward_once, x, true)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject module-alias wrappers when post-forward non-alias lets contain calls",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_result_alias_with_callful_nonalias_let(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-result-callful-nonalias-let",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_result_with_callful_nonalias_let(f: fn(Unique Int) -> Unique Int, x: Unique Int, flag: Bool) -> Unique Int\n  let out0 = f(x)\n  let keep = bool_id(flag)\n  let out1 = out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_result_with_callful_nonalias_let, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_result_with_callful_nonalias_let(forward_once, x, true)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject named-import wrappers when post-forward non-alias lets contain calls",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_with_callful_prelude_let() {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_with_callful_prelude_setup(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = bool_id(flag)\n  let y = x\n  let out = f(y)\n  out\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_with_callful_prelude_setup(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-callful-prelude-let",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject wrappers when pre-forward setup lets contain calls",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_with_callful_prelude_let() {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-callful-prelude-let",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_with_callful_prelude_setup(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = bool_id(flag)\n  let y = x\n  let out = f(y)\n  out\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_with_callful_prelude_setup(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject module-alias wrappers when pre-forward setup lets contain calls",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_with_callful_prelude_let() {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-callful-prelude-let",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_with_callful_prelude_setup(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = bool_id(flag)\n  let y = x\n  let out = f(y)\n  out\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_with_callful_prelude_setup, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_with_callful_prelude_setup(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject named-import wrappers when pre-forward setup lets contain calls",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_forwarder_combo_alias_with_callful_prelude_and_result_if_condition(
) {
    let source_path = write_temp_source(
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_combo_alias_with_callful_prelude_and_result_if_condition(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = bool_id(flag)\n  let y = x\n  let out0 = f(y)\n  let out1 = if bool_id(seed)\n    out0\n  else\n    out0\n  out1\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_alias_with_callful_prelude_and_result_if_condition(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-higher-order-forwarder-combo-callful-prelude-result-if",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject wrappers when both pre-forward setup and post-forward result-if shaping are callful",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_module_alias_wrapper_combo_alias_with_callful_prelude_and_result_if_condition(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-alias-combo-callful-prelude-result-if",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_combo_alias_with_callful_prelude_and_result_if_condition(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = bool_id(flag)\n  let y = x\n  let out0 = f(y)\n  let out1 = if bool_id(seed)\n    out0\n  else\n    out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha as A\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  A.apply_combo_alias_with_callful_prelude_and_result_if_condition(true, A.forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject module-alias wrappers when both pre-forward setup and post-forward result-if shaping are callful",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_unique_higher_order_named_import_wrapper_combo_alias_with_callful_prelude_and_result_if_condition(
) {
    let project_dir = temp_workspace_project_dir(
        "kea-cli-fip-unique-higher-order-named-combo-callful-prelude-result-if",
    );
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");
    let source_path = src_dir.join("main.kea");
    std::fs::write(
        src_dir.join("alpha.kea"),
        "fn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn bool_id(flag: Bool) -> Bool\n  flag\n\nfn apply_combo_alias_with_callful_prelude_and_result_if_condition(flag: Bool, f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let seed = bool_id(flag)\n  let y = x\n  let out0 = f(y)\n  let out1 = if bool_id(seed)\n    out0\n  else\n    out0\n  out1\n",
    )
    .expect("alpha module write should succeed");
    std::fs::write(
        &source_path,
        "use Alpha.{apply_combo_alias_with_callful_prelude_and_result_if_condition, forward_once}\n\n@fip\nfn call_via_apply(x: Unique Int) -> Unique Int\n  apply_combo_alias_with_callful_prelude_and_result_if_condition(true, forward_once, x)\n\nfn main() -> Int\n  0\n",
    )
    .expect("source write should succeed");

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject named-import wrappers when both pre-forward setup and post-forward result-if shaping are callful",
    );
    assert!(
        err.contains("`@fip` verification failed for `call_via_apply`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("Unique parameter `x` escapes through 1 call argument(s)"),
        "expected escape diagnostic for `x`, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_fip_unique_branch_handoff_exit_code() {
    let source_path = write_temp_source(
        "@fip\nfn dup_branch(x: Unique Int, pick_left: Bool) -> Unique Int\n  if pick_left\n    x\n  else\n    x\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-branch-handoff",
        "kea",
    );

    let run = run_file(&source_path)
        .expect("@fip verifier should accept branch-exclusive unique handoff");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_unique_param_escapes_via_call() {
    let source_path = write_temp_source(
        "@fip\nfn forward_via_call(x: Unique Int, f: fn(Unique Int) -> Int) -> Int\n  f(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-call-escape",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("@fip verifier should reject unique call-boundary escape");
    assert!(
        err.contains("`@fip` verification failed for `forward_via_call`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("escapes through") && err.contains("call argument"),
        "expected call-boundary ownership-flow detail, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_unique_alias_escapes_via_call() {
    let source_path = write_temp_source(
        "@fip\nfn alias_forward_via_call(x: Unique Int, f: fn(Unique Int) -> Int) -> Int\n  let y = x\n  f(y)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unique-alias-call-escape",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("@fip verifier should reject aliased unique call-boundary escape");
    assert!(
        err.contains("`@fip` verification failed for `alias_forward_via_call`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("escapes through") && err.contains("call argument"),
        "expected aliased call-boundary ownership-flow detail, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_call_boundary_is_unproven() {
    let source_path = write_temp_source(
        "struct Box\n  n: Int\n\nfn alloc_inner(x: Int) -> Int\n  let b = Box { n: x }\n  b.n\n\n@fip\nfn outer(x: Int) -> Int\n  alloc_inner(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unproven-call-boundary",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject cross-function calls without a verified handoff proof",
    );
    assert!(
        err.contains("`@fip` verification failed for `outer`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("unsupported_call_boundaries="),
        "expected unsupported call-boundary detail in @fip diagnostics, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_function_body_contains_raw_hir_expr() {
    let source_path = write_temp_source(
        "@fip\nfn raw_when_guard_passthrough(x: Unique Int) -> Unique Int\n  x when true\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-raw-hir-body",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("@fip verifier should reject functions that still contain raw HIR fallback nodes");
    assert!(
        err.contains("`@fip` verification failed for `raw_when_guard_passthrough`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("raw_hir_expr_count="),
        "expected raw HIR fallback detail in diagnostics, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_candidate_safe_forwarder_allocates() {
    let source_path = write_temp_source(
        "struct Box\n  n: Int\n\nfn alloc_and_return(x: Unique Int) -> Unique Int\n  let b = Box { n: 1 }\n  x\n\n@fip\nfn outer(x: Unique Int) -> Unique Int\n  alloc_and_return(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-candidate-forwarder-allocates",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject cross-function handoff proofs through allocating callees",
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unproven call-boundary count in diagnostics, got: {err}"
    );
    assert!(
        err.contains("alloc_and_return"),
        "expected rejected call-boundary site in diagnostics, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_candidate_safe_forwarder_makes_unrelated_call() {
    let source_path = write_temp_source(
        "fn helper() -> Int\n  1\n\nfn calls_then_returns(x: Unique Int) -> Unique Int\n  let t = helper()\n  x\n\n@fip\nfn outer(x: Unique Int) -> Unique Int\n  calls_then_returns(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-candidate-forwarder-calls-helper",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject cross-function handoff proofs through callees that make nested calls",
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unproven call-boundary count in diagnostics, got: {err}"
    );
    assert!(
        err.contains("calls_then_returns"),
        "expected rejected call-boundary site in diagnostics, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_candidate_higher_order_wrapper_allocates() {
    let source_path = write_temp_source(
        "struct Box\n  n: Int\n\nfn forward_once(x: Unique Int) -> Unique Int\n  x\n\nfn apply_with_alloc(f: fn(Unique Int) -> Unique Int, x: Unique Int) -> Unique Int\n  let b = Box { n: 1 }\n  f(x)\n\n@fip\nfn outer(x: Unique Int) -> Unique Int\n  apply_with_alloc(forward_once, x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-candidate-ho-wrapper-allocates",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject higher-order wrapper proofs through allocating wrappers",
    );
    assert!(
        err.contains("unsupported_call_boundaries=1"),
        "expected unproven call-boundary count in diagnostics, got: {err}"
    );
    assert!(
        err.contains("apply_with_alloc"),
        "expected rejected call-boundary site in diagnostics, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_call_boundary_is_unproven_reports_site_occurrences() {
    let source_path = write_temp_source(
        "struct Box\n  n: Int\n\nfn alloc_inner(x: Int) -> Int\n  let b = Box { n: x }\n  b.n\n\n@fip\nfn outer(x: Int) -> Int\n  alloc_inner(x)\n  alloc_inner(x)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-unproven-call-boundary-occurrences",
        "kea",
    );

    let err = run_file(&source_path).expect_err(
        "@fip verifier should reject repeated unproven call boundaries and summarize repeated sites",
    );
    assert!(
        err.contains("unsupported_call_boundaries=2"),
        "expected unsupported call-boundary count in @fip diagnostics, got: {err}"
    );
    assert!(
        err.contains("alloc_inner (2 occurrences)"),
        "expected repeated call-boundary site summary, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_allocations_remain() {
    let source_path = write_temp_source(
        "enum Chain\n  End\n  Link(Int, Chain)\n\n@fip\nfn build(n: Int) -> Chain\n  if n <= 0\n    Chain.End\n  else\n    Chain.Link(n, build(n - 1))\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-reject-allocating",
        "kea",
    );

    let err = run_file(&source_path).expect_err("@fip verifier should reject allocating function");
    assert!(
        err.contains("`@fip` verification failed for `build`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("first offending MIR sites"),
        "expected site-level @fip diagnostics, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_when_closure_alloc_remains() {
    let source_path = write_temp_source(
        "@fip\nfn closure_alloc(delta: Int) -> Int\n  let add = |x| x + delta\n  add(1)\n\nfn main() -> Int\n  0\n",
        "kea-cli-fip-reject-closure-alloc",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("@fip verifier should reject closure-allocating function");
    assert!(
        err.contains("`@fip` verification failed for `closure_alloc`"),
        "expected @fip verification failure, got: {err}"
    );
    assert!(
        err.contains("ClosureInit"),
        "expected closure-allocation site in diagnostics, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_fip_annotation_with_arguments() {
    let source_path = write_temp_source(
        "@fip(\"strict\")\nfn id(x: Int) -> Int\n  x\n\nfn main() -> Int\n  id(1)\n",
        "kea-cli-fip-args-invalid",
        "kea",
    );

    let err = run_file(&source_path).expect_err("@fip annotation with args should fail validation");
    assert!(
        err.contains("`@fip` does not accept arguments"),
        "expected @fip argument validation failure, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_accepts_unsafe_annotation_on_function() {
    let source_path = write_temp_source(
        "@unsafe\nfn raw_add_one(x: Int) -> Int\n  x + 1\n\n@unsafe\nfn main() -> Int\n  raw_add_one(41)\n",
        "kea-cli-unsafe-annotation-function",
        "kea",
    );

    let run = run_file(&source_path).expect("@unsafe function annotation should be accepted");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_calling_unsafe_function_from_safe_context() {
    let source_path = write_temp_source(
        "@unsafe\nfn raw_add_one(x: Int) -> Int\n  x + 1\n\nfn main() -> Int\n  raw_add_one(1)\n",
        "kea-cli-unsafe-call-safe-context",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("safe function should not be able to call @unsafe callee");
    assert!(
        err.contains("call to `@unsafe` function `raw_add_one` requires unsafe context"),
        "expected unsafe call-site diagnostic, got: {err}"
    );
    assert!(
        err.contains("enclosing function `main` is safe"),
        "expected caller-context help message, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_accepts_calling_unsafe_function_inside_unsafe_block() {
    let source_path = write_temp_source(
        "@unsafe\nfn raw_add_one(x: Int) -> Int\n  x + 1\n\nfn main() -> Int\n  unsafe\n    raw_add_one(41)\n",
        "kea-cli-unsafe-block-safe-caller",
        "kea",
    );

    let run = run_file(&source_path).expect("unsafe block should permit @unsafe call from safe fn");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_accepts_calling_unsafe_function_inside_inline_unsafe_expression() {
    let source_path = write_temp_source(
        "@unsafe\nfn raw_add_one(x: Int) -> Int\n  x + 1\n\nfn main() -> Int\n  unsafe raw_add_one(41)\n",
        "kea-cli-unsafe-inline-safe-caller",
        "kea",
    );

    let run = run_file(&source_path)
        .expect("inline unsafe expression should permit @unsafe call from safe fn");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_calling_imported_unsafe_function_from_safe_context() {
    let project_dir = temp_project_dir("kea-cli-unsafe-import-qualified");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    std::fs::write(
        src_dir.join("raw.kea"),
        "@unsafe\nfn raw_add_one(x: Int) -> Int\n  x + 1\n",
    )
    .expect("raw module write should succeed");
    let app_path = src_dir.join("app.kea");
    std::fs::write(&app_path, "use Raw\nfn main() -> Int\n  Raw.raw_add_one(1)\n")
        .expect("app module write should succeed");

    let err = run_file(&app_path)
        .expect_err("safe function should not be able to call imported @unsafe callee");
    assert!(
        err.contains("call to `@unsafe` function `Raw.raw_add_one` requires unsafe context"),
        "expected imported unsafe call-site diagnostic, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_calling_named_imported_unsafe_function_from_safe_context() {
    let project_dir = temp_project_dir("kea-cli-unsafe-import-named");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    std::fs::write(
        src_dir.join("raw.kea"),
        "@unsafe\nfn raw_add_one(x: Int) -> Int\n  x + 1\n",
    )
    .expect("raw module write should succeed");
    let app_path = src_dir.join("app.kea");
    std::fs::write(&app_path, "use Raw.{raw_add_one}\nfn main() -> Int\n  raw_add_one(1)\n")
        .expect("app module write should succeed");

    let err = run_file(&app_path)
        .expect_err("safe function should not be able to call named-imported @unsafe callee");
    assert!(
        err.contains("call to `@unsafe` function `raw_add_one` requires unsafe context"),
        "expected named-import unsafe call-site diagnostic, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_accepts_calling_imported_unsafe_function_inside_unsafe_block() {
    let project_dir = temp_project_dir("kea-cli-unsafe-import-local-block");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    std::fs::write(
        src_dir.join("raw.kea"),
        "@unsafe\nfn raw_add_one(x: Int) -> Int\n  x + 1\n",
    )
    .expect("raw module write should succeed");
    let app_path = src_dir.join("app.kea");
    std::fs::write(
        &app_path,
        "use Raw\nfn main() -> Int\n  unsafe\n    Raw.raw_add_one(41)\n",
    )
    .expect("app module write should succeed");

    let run =
        run_file(&app_path).expect("unsafe block should permit imported @unsafe call from safe fn");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_accepts_builtin_ptr_is_null_in_safe_context() {
    let source_path = write_temp_source(
        "fn check(p: Ptr Int) -> Bool\n  Ptr.is_null(p)\n\nfn main() -> Int\n  0\n",
        "kea-cli-ptr-is-null-safe",
        "kea",
    );

    let run = run_file(&source_path).expect("Ptr.is_null should be callable in safe context");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_builtin_ptr_read_from_safe_context() {
    let source_path = write_temp_source(
        "fn read_ptr(p: Ptr Int) -> Int\n  Ptr.read(p)\n\nfn main() -> Int\n  0\n",
        "kea-cli-ptr-read-safe-reject",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("Ptr.read should require unsafe context in safe functions");
    assert!(
        err.contains("call to `@unsafe` function `Ptr.read` requires unsafe context"),
        "expected unsafe diagnostic for Ptr.read, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_accepts_builtin_ptr_read_inside_inline_unsafe_expression() {
    let source_path = write_temp_source(
        "fn read_ptr(p: Ptr Int) -> Int\n  unsafe Ptr.read(p)\n\nfn main() -> Int\n  0\n",
        "kea-cli-ptr-read-unsafe-inline",
        "kea",
    );

    let run = run_file(&source_path).expect("unsafe Ptr.read call should compile");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_accepts_builtin_ptr_null_inside_inline_unsafe_expression() {
    let source_path = write_temp_source(
        "fn null_ptr() -> Ptr Int\n  unsafe Ptr.null()\n\nfn main() -> Int\n  0\n",
        "kea-cli-ptr-null-unsafe-inline",
        "kea",
    );

    let run = run_file(&source_path).expect("unsafe Ptr.null call should compile");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_builtin_ptr_alloc_from_safe_context() {
    let source_path = write_temp_source(
        "fn alloc_ptr() -> Ptr Int\n  Ptr.alloc(1)\n\nfn main() -> Int\n  0\n",
        "kea-cli-ptr-alloc-safe-reject",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("Ptr.alloc should require unsafe context in safe functions");
    assert!(
        err.contains("call to `@unsafe` function `Ptr.alloc` requires unsafe context"),
        "expected unsafe diagnostic for Ptr.alloc, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_builtin_ptr_alloc_read_write_free_exit_code() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  unsafe\n    let p = Ptr.alloc(1)\n    Ptr.write(p, 42)\n    let value = Ptr.read(p)\n    Ptr.free(p)\n    value\n",
        "kea-cli-ptr-alloc-read-write-free",
        "kea",
    );

    let run = run_file(&source_path).expect("Ptr alloc/read/write/free should execute");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_builtin_ptr_offset_second_slot_exit_code() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  unsafe\n    let p = Ptr.alloc(2)\n    Ptr.write(p, 10)\n    let p1 = Ptr.offset(p, 1)\n    Ptr.write(p1, 20)\n    let total = Ptr.read(p) + Ptr.read(p1)\n    Ptr.free(p)\n    total\n",
        "kea-cli-ptr-offset-slot",
        "kea",
    );

    let run = run_file(&source_path).expect("Ptr.offset should advance by element size");
    assert_eq!(run.exit_code, 30);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_builtin_ptr_cast_round_trip_exit_code() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  unsafe\n    let p = Ptr.alloc(1)\n    let q: Ptr Int = Ptr.cast(p)\n    Ptr.write(q, 7)\n    let value = Ptr.read(q)\n    Ptr.free(q)\n    value\n",
        "kea-cli-ptr-cast-round-trip",
        "kea",
    );

    let run = run_file(&source_path).expect("Ptr.cast should preserve pointer value");
    assert_eq!(run.exit_code, 7);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_unsafe_annotation_with_arguments() {
    let source_path = write_temp_source(
        "@unsafe(\"strict\")\nfn raw_add_one(x: Int) -> Int\n  x + 1\n\nfn main() -> Int\n  raw_add_one(1)\n",
        "kea-cli-unsafe-annotation-args",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("@unsafe annotation with args should fail validation");
    assert!(
        err.contains("`@unsafe` does not accept arguments"),
        "expected @unsafe argument validation failure, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_unsafe_annotation_on_record_declaration() {
    let source_path = write_temp_source(
        "@unsafe\nstruct Box\n  value: Int\n\nfn main() -> Int\n  0\n",
        "kea-cli-unsafe-annotation-record",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("@unsafe annotation on record declaration should fail validation");
    assert!(
        err.contains("`@unsafe` is not valid on record declaration"),
        "expected @unsafe target validation failure, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_accepts_unboxed_annotation_on_struct() {
    let source_path = write_temp_source(
        "@unboxed\nstruct Pair\n  left: Int\n  right: Int\n\nfn main() -> Int\n  let p = Pair { left: 20, right: 22 }\n  p.left + p.right\n",
        "kea-cli-unboxed-struct-accept",
        "kea",
    );

    let run = run_file(&source_path).expect("@unboxed struct with value fields should compile");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_unboxed_annotation_with_arguments() {
    let source_path = write_temp_source(
        "@unboxed(\"flat\")\nstruct Pair\n  left: Int\n  right: Int\n\nfn main() -> Int\n  0\n",
        "kea-cli-unboxed-annotation-args",
        "kea",
    );

    let err = run_file(&source_path).expect_err("@unboxed annotation with args should fail");
    assert!(
        err.contains("`@unboxed` does not accept arguments"),
        "expected @unboxed argument validation failure, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_unboxed_annotation_on_function() {
    let source_path = write_temp_source(
        "@unboxed\nfn bad(x: Int) -> Int\n  x\n\nfn main() -> Int\n  bad(1)\n",
        "kea-cli-unboxed-annotation-function",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("@unboxed annotation on function should fail validation");
    assert!(
        err.contains("`@unboxed` is not valid on function declaration"),
        "expected @unboxed target validation failure, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_rejects_unboxed_struct_with_heap_field() {
    let source_path = write_temp_source(
        "@unboxed\nstruct Bad\n  name: String\n\nfn main() -> Int\n  0\n",
        "kea-cli-unboxed-heap-field-reject",
        "kea",
    );

    let err = run_file(&source_path).expect_err("@unboxed struct with heap fields should fail");
    assert!(
        err.contains("`@unboxed` field `name` must be a value type"),
        "expected @unboxed value-type diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_unboxed_local_record_elides_heap_alloc_in_stats() {
    let source_path = write_temp_source(
        "@unboxed\nstruct Pair\n  left: Int\n  right: Int\n\nfn main() -> Int\n  let p = Pair { left: 20, right: 22 }\n  p.left + p.right\n",
        "kea-cli-unboxed-local-no-alloc-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    let app_main_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "main" || f.function.ends_with(".main"))
        .collect::<Vec<_>>();
    assert!(
        !app_main_stats.is_empty(),
        "expected app main stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = app_main_stats.iter().map(|f| f.alloc_count).sum();
    let retain_count: usize = app_main_stats.iter().map(|f| f.retain_count).sum();
    let release_count: usize = app_main_stats.iter().map(|f| f.release_count).sum();

    assert_eq!(
        alloc_count, 0,
        "expected no heap alloc ops for non-escaping @unboxed kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        retain_count, 0,
        "expected no retain ops for non-escaping @unboxed kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        release_count, 0,
        "expected no release ops for non-escaping @unboxed kernel, stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_unboxed_local_record_move_alias_elides_heap_alloc_in_stats() {
    let source_path = write_temp_source(
        "@unboxed\nstruct Pair\n  left: Int\n  right: Int\n\nfn main() -> Int\n  let p0 = Pair { left: 20, right: 22 }\n  let p1 = p0\n  p1.left + p1.right\n",
        "kea-cli-unboxed-local-alias-no-alloc-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    let app_main_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "main" || f.function.ends_with(".main"))
        .collect::<Vec<_>>();
    assert!(
        !app_main_stats.is_empty(),
        "expected app main stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = app_main_stats.iter().map(|f| f.alloc_count).sum();
    let retain_count: usize = app_main_stats.iter().map(|f| f.retain_count).sum();
    let release_count: usize = app_main_stats.iter().map(|f| f.release_count).sum();

    assert_eq!(
        alloc_count, 0,
        "expected no heap alloc ops for non-escaping @unboxed alias kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        retain_count, 0,
        "expected no retain ops for non-escaping @unboxed alias kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        release_count, 0,
        "expected no release ops for non-escaping @unboxed alias kernel, stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_unboxed_local_record_if_join_elides_heap_alloc_in_stats() {
    let source_path = write_temp_source(
        "@unboxed\nstruct Pair\n  left: Int\n  right: Int\n\nfn main() -> Int\n  let p = Pair { left: 20, right: 22 }\n  let q = if p.left == 20\n    p\n  else\n    p\n  q.left + q.right\n",
        "kea-cli-unboxed-local-if-join-no-alloc-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    let app_main_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "main" || f.function.ends_with(".main"))
        .collect::<Vec<_>>();
    assert!(
        !app_main_stats.is_empty(),
        "expected app main stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = app_main_stats.iter().map(|f| f.alloc_count).sum();
    let retain_count: usize = app_main_stats.iter().map(|f| f.retain_count).sum();
    let release_count: usize = app_main_stats.iter().map(|f| f.release_count).sum();

    assert_eq!(
        alloc_count, 0,
        "expected no heap alloc ops for non-escaping @unboxed if-join kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        retain_count, 0,
        "expected no retain ops for non-escaping @unboxed if-join kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        release_count, 0,
        "expected no release ops for non-escaping @unboxed if-join kernel, stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_local_payload_sum_case_elides_heap_alloc_in_stats() {
    let source_path = write_temp_source(
        "enum Pairish\n  Pair(Int, Int)\n  Swap(Int, Int)\n\nfn main() -> Int\n  let p = Pairish.Pair(20, 22)\n  case p\n    Pairish.Pair(a, b) -> a + b\n    Pairish.Swap(a, b) -> a + b\n",
        "kea-cli-payload-sum-local-no-alloc-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    let app_main_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "main" || f.function.ends_with(".main"))
        .collect::<Vec<_>>();
    assert!(
        !app_main_stats.is_empty(),
        "expected app main stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = app_main_stats.iter().map(|f| f.alloc_count).sum();
    let retain_count: usize = app_main_stats.iter().map(|f| f.retain_count).sum();
    let release_count: usize = app_main_stats.iter().map(|f| f.release_count).sum();

    assert_eq!(
        alloc_count, 0,
        "expected no heap alloc ops for non-escaping payload-sum kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        retain_count, 0,
        "expected no retain ops for non-escaping payload-sum kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        release_count, 0,
        "expected no release ops for non-escaping payload-sum kernel, stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_local_payload_sum_if_join_elides_heap_alloc_in_stats() {
    let source_path = write_temp_source(
        "enum Pairish\n  Pair(Int, Int)\n  Swap(Int, Int)\n\nfn main() -> Int\n  let p = Pairish.Pair(20, 22)\n  let q = if 1 == 1\n    p\n  else\n    p\n  case q\n    Pairish.Pair(a, b) -> a + b\n    Pairish.Swap(a, b) -> a + b\n",
        "kea-cli-payload-sum-if-join-no-alloc-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    let app_main_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "main" || f.function.ends_with(".main"))
        .collect::<Vec<_>>();
    assert!(
        !app_main_stats.is_empty(),
        "expected app main stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = app_main_stats.iter().map(|f| f.alloc_count).sum();
    let retain_count: usize = app_main_stats.iter().map(|f| f.retain_count).sum();
    let release_count: usize = app_main_stats.iter().map(|f| f.release_count).sum();

    assert_eq!(
        alloc_count, 0,
        "expected no heap alloc ops for non-escaping payload-sum if-join kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        retain_count, 0,
        "expected no retain ops for non-escaping payload-sum if-join kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        release_count, 0,
        "expected no release ops for non-escaping payload-sum if-join kernel, stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_local_payload_sum_if_join_call_escape_counts_alloc_in_stats() {
    let source_path = write_temp_source(
        "enum Pairish\n  Pair(Int, Int)\n  Swap(Int, Int)\n\nfn sink(p: Pairish) -> Int\n  case p\n    Pairish.Pair(a, b) -> a + b\n    Pairish.Swap(a, b) -> a + b\n\nfn main() -> Int\n  let p = Pairish.Pair(20, 22)\n  let q = if 1 == 1\n    p\n  else\n    p\n  sink(q)\n",
        "kea-cli-payload-sum-if-join-call-escape-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    let app_main_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "main" || f.function.ends_with(".main"))
        .collect::<Vec<_>>();
    assert!(
        !app_main_stats.is_empty(),
        "expected app main stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = app_main_stats.iter().map(|f| f.alloc_count).sum();
    assert!(
        alloc_count >= 1,
        "expected heap alloc ops for payload-sum call-escape path, stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_local_mixed_sum_kernel_elides_alloc_and_release_in_stats() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  case Some(20)\n    Some(v) -> v\n    None -> 0\n",
        "kea-cli-mixed-sum-direct-case-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    let app_main_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "main" || f.function.ends_with(".main"))
        .collect::<Vec<_>>();
    assert!(
        !app_main_stats.is_empty(),
        "expected app main stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = app_main_stats.iter().map(|f| f.alloc_count).sum();
    assert_eq!(
        alloc_count, 0,
        "expected no heap alloc ops for local mixed sum kernel, stats: {:?}",
        compiled.stats
    );
    let release_count: usize = app_main_stats.iter().map(|f| f.release_count).sum();
    assert_eq!(
        release_count, 0,
        "expected no release ops for stack-lowered local mixed sum kernel, stats: {:?}",
        compiled.stats
    );
    let mixed_excluded_count: usize = app_main_stats
        .iter()
        .map(|f| f.stack_sum_mixed_excluded_count)
        .sum();
    assert_eq!(
        mixed_excluded_count, 0,
        "expected no mixed-layout stack exclusion after mixed-sum eligibility widening, stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 20);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_mixed_sum_if_join_kernel_elides_alloc_and_release_in_stats() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  let opt = if 1 == 1\n    Some(20)\n  else\n    None\n  case opt\n    Some(v) -> v\n    None -> 0\n",
        "kea-cli-mixed-sum-if-join-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    let app_main_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "main" || f.function.ends_with(".main"))
        .collect::<Vec<_>>();
    assert!(
        !app_main_stats.is_empty(),
        "expected app main stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = app_main_stats.iter().map(|f| f.alloc_count).sum();
    assert_eq!(
        alloc_count, 0,
        "expected no heap alloc ops for if-join mixed sum kernel, stats: {:?}",
        compiled.stats
    );
    let release_count: usize = app_main_stats.iter().map(|f| f.release_count).sum();
    assert_eq!(
        release_count, 0,
        "expected no release ops for stack-lowered if-join mixed sum kernel, stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 20);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_value_only_record_if_join_reduces_consume_alloc_in_stats() {
    let source_path = write_temp_source(
        "struct Point\n  x: Int\n\nfn consume(flag: Bool, p: Point) -> Unit\n  let q = if flag\n    p\n  else\n    Point { x: 1 }\n  let out = Point { x: q.x + 1 }\n  ()\n\nfn main() -> Int\n  consume(true, Point { x: 0 })\n  consume(false, Point { x: 0 })\n  0\n",
        "kea-cli-value-only-record-if-join-reuse-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    let consume_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "consume" || f.function.ends_with(".consume"))
        .collect::<Vec<_>>();
    assert!(
        !consume_stats.is_empty(),
        "expected consume stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = consume_stats.iter().map(|f| f.alloc_count).sum();
    assert!(
        alloc_count <= 2,
        "expected value-only record if-join consume path to keep alloc count at most one per lowered function, stats: {:?}",
        compiled.stats
    );
    let release_count: usize = consume_stats.iter().map(|f| f.release_count).sum();
    let reuse_token_produced: usize = consume_stats.iter().map(|f| f.reuse_token_produced_count).sum();
    // After the reuse fix, consume correctly releases its input param (p or the reused slot).
    // The join block always has Release(q); the false branch also produces a ReuseToken for p.
    // Each consume function entry contributes exactly 1 plain release (Release(q) in the join block).
    let plain_releases = release_count.saturating_sub(reuse_token_produced);
    assert_eq!(
        plain_releases, consume_stats.len(),
        "expected exactly one plain release per consume function entry (join-block param), with all other releases being reuse tokens, stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_loop_mixed_unit_walk_keeps_record_alloc_floor_in_stats() {
    let source_path = write_temp_source(
        "struct Point\n  x: Int\n\nfn walk(n: Int, p: Point) -> Unit\n  let cur = if n % 2 == 0\n    p\n  else\n    Point { x: p.x + 1 }\n  if n <= 0\n    ()\n  else\n    walk(n - 1, cur)\n\nfn main() -> Int\n  walk(64, Point { x: 0 })\n  0\n",
        "kea-cli-loop-mixed-unit-walk-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    let app_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "walk" || f.function == "main")
        .collect::<Vec<_>>();
    assert!(
        !app_stats.is_empty(),
        "expected app walk/main stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = app_stats.iter().map(|f| f.alloc_count).sum();
    assert!(
        alloc_count <= 1,
        "expected loop mixed-unit walk kernel to drop app alloc floor to <=1 after guarded tail-self stack forwarding, stats: {:?}",
        compiled.stats
    );
    let walk_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "walk")
        .collect::<Vec<_>>();
    assert!(
        !walk_stats.is_empty(),
        "expected walk stats to exist, stats: {:?}",
        compiled.stats
    );
    let walk_alloc_count: usize = walk_stats.iter().map(|f| f.alloc_count).sum();
    assert_eq!(
        walk_alloc_count, 0,
        "expected loop mixed-unit walk core path to be stack-lowered (0 walk allocs), stats: {:?}",
        compiled.stats
    );
    let release_count: usize = app_stats.iter().map(|f| f.release_count).sum();
    let reuse_token_produced: usize = app_stats.iter().map(|f| f.reuse_token_produced_count).sum();
    assert_eq!(
        release_count, reuse_token_produced,
        "expected all releases in loop mixed-unit walk kernel to be reuse tokens (no wasted releases), stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_unboxed_struct_emits_no_retain_release_in_stats() {
    let source_path = write_temp_source(
        "@unboxed\nstruct Pair\n  left: Int\n  right: Int\n\nfn mk(n: Int) -> Pair\n  Pair { left: n, right: n + 1 }\n\nfn main() -> Int\n  let p0 = mk(20)\n  let p1 = p0\n  p1.left + p1.right\n",
        "kea-cli-unboxed-stats",
        "kea",
    );

    let compiled = compile_file(&source_path, CodegenMode::Jit).expect("compile should work");
    // Only check functions from the user source — stdlib functions (e.g. List.nth, which
    // correctly releases polymorphic sum-type bindings in guard-fail paths) are excluded.
    let user_fns: Vec<_> = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| matches!(f.function.as_str(), "mk" | "main"))
        .collect();
    let retain_count: usize = user_fns.iter().map(|f| f.retain_count).sum();
    let release_count: usize = user_fns.iter().map(|f| f.release_count).sum();
    assert_eq!(
        retain_count, 0,
        "expected no retain ops for @unboxed-only kernel, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        release_count, 0,
        "expected no release ops for @unboxed-only kernel, stats: {:?}",
        compiled.stats
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 41);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_build_and_execute_aot_ptr_alloc_read_write_free_exit_code() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  unsafe\n    let p = Ptr.alloc(1)\n    Ptr.write(p, 42)\n    let value = Ptr.read(p)\n    Ptr.free(p)\n    value\n",
        "kea-cli-aot-ptr-alloc-read-write-free",
        "kea",
    );
    let output_path = temp_artifact_path("kea-cli-aot-ptr-alloc-read-write-free", "bin");

    let compiled = compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
    link_object_bytes(&compiled.object, &output_path).expect("link should work");

    let status = std::process::Command::new(&output_path)
        .status()
        .expect("aot executable should run");
    assert_eq!(status.code(), Some(42));

    let _ = std::fs::remove_file(source_path);
    let _ = std::fs::remove_file(output_path);
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

    let compiled = compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
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

    let compiled = compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
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

    let compiled = compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
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

    let compiled = compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
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

    let compiled = compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
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

        let jit = run_file(&source_path)
            .unwrap_or_else(|err| panic!("jit run should succeed for parity case {idx}: {err}"));
        assert_eq!(
            jit.exit_code, *expected_exit,
            "jit exit mismatch for parity case {idx}"
        );

        let output_path = temp_artifact_path(&name, "bin");
        let compiled = compile_file(&source_path, CodegenMode::Aot)
            .unwrap_or_else(|err| panic!("aot compile should work for parity case {idx}: {err}"));
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
    let source_path = write_temp_source("fn main() -> Int8\n  42\n", "kea-cli-int8-main", "kea");

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

    let run = run_file(&source_path).expect("UInt8.try_from negative should return None");
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
fn compile_rejects_division_by_zero_literal() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  1 / 0\n",
        "kea-cli-div-by-zero-literal",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("division by zero literal should fail at compile time");
    assert!(
        err.contains("division by zero is not allowed"),
        "expected division-by-zero diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_modulo_by_zero_literal() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  7 % 0\n",
        "kea-cli-mod-by-zero-literal",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("modulo by zero literal should fail at compile time");
    assert!(
        err.contains("modulo by zero is not allowed"),
        "expected modulo-by-zero diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_state_effect_payload_with_unique_type() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\ntype UniqueInt = Unique(Int)\n\neffect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn bad() -[State UniqueInt]> Int\n  0\n\nfn main() -> Int\n  0\n",
        "kea-cli-state-unique-effect-payload",
        "kea",
    );

    let err = run_file(&source_path).expect_err("State payload containing Unique should fail");
    assert!(
        err.contains("State effect payload cannot contain `Unique`"),
        "expected State/Unique payload diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_state_effect_payload_with_nested_unique_type() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\ntype Wrapped = { value: Unique(Int), tag: Int }\n\neffect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn bad() -[State Wrapped]> Int\n  0\n\nfn main() -> Int\n  0\n",
        "kea-cli-state-nested-unique-effect-payload",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("State payload containing nested Unique should fail");
    assert!(
        err.contains("State effect payload cannot contain `Unique`"),
        "expected State/Unique payload diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_unique_roundtrip_through_tail_resumptive_handler_exit_code() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\ntype UniqueInt = Unique(Int)\n\neffect Echo A\n  fn echo(value: A) -> A\n\nfn roundtrip(value: UniqueInt) -[Echo UniqueInt]> Int\n  let out = Echo.echo(value)\n  case out\n    Unique(v) -> v\n\nfn main() -> Int\n  handle roundtrip(Unique(7))\n    Echo.echo(v) -> resume v\n",
        "kea-cli-unique-tail-handler-roundtrip",
        "kea",
    );

    let run = run_file(&source_path).expect(
        "Unique values should flow through tail-resumptive handlers when ownership is resumed exactly once",
    );
    assert_eq!(run.exit_code, 7);

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
fn compile_rejects_consuming_borrow_parameter_in_handler_clause() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\neffect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn bad(borrow value: Unique Int) -> Int\n  handle State.get()\n    State.get() ->\n      case value\n        Unique(v) -> v\n    State.put(next) -> resume ()\n\nfn main() -> Int\n  0\n",
        "kea-cli-borrow-handler-clause-consume-rejected",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("consuming borrowed parameter in handler clause should fail");
    assert!(
        err.contains("borrowed value `value` cannot be consumed"),
        "expected borrow-consumption diagnostic in handler clause, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_consuming_borrow_parameter_in_handler_clause_through_alias() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\neffect Tick\n  fn step() -> Unit\n\nfn consume(v: Unique Int) -> Unit\n  ()\n\nfn bad(borrow value: Unique Int) -[Tick]> Unit\n  handle Tick.step()\n    Tick.step() ->\n      let forwarded = value\n      consume(forwarded)\n      resume ()\n\nfn main() -> Int\n  0\n",
        "kea-cli-borrow-handler-clause-alias-consume-rejected",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("consuming borrowed parameter in handler clause through alias should fail");
    assert!(
        err.contains("borrowed value") && err.contains("cannot be consumed"),
        "expected borrow-consumption diagnostic in handler clause alias path, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_consuming_borrow_parameter_in_then_clause() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\neffect Dummy\n  fn noop() -> Unit\n\nfn bad(borrow value: Unique Int) -> Int\n  handle Dummy.noop()\n    Dummy.noop() -> resume ()\n    then result ->\n      case value\n        Unique(v) -> v\n\nfn main() -> Int\n  0\n",
        "kea-cli-borrow-then-clause-consume-rejected",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("consuming borrowed parameter in then clause should fail");
    assert!(
        err.contains("borrowed value `value` cannot be consumed"),
        "expected borrow-consumption diagnostic in then clause, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_consuming_borrow_parameter_in_then_clause_through_alias() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\neffect Dummy\n  fn noop() -> Unit\n\nfn bad(borrow value: Unique Int) -> Int\n  handle Dummy.noop()\n    Dummy.noop() -> resume ()\n    then result ->\n      let forwarded = value\n      case forwarded\n        Unique(v) -> v\n\nfn main() -> Int\n  0\n",
        "kea-cli-borrow-then-clause-alias-consume-rejected",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("consuming borrowed parameter in then clause through alias should fail");
    assert!(
        err.contains("borrowed value") && err.contains("cannot be consumed"),
        "expected borrow-consumption diagnostic in then clause alias path, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_passing_borrow_parameter_into_effect_operation() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\ntype UniqueInt = Unique(Int)\n\neffect Echo A\n  fn echo(value: A) -> A\n\nfn bad(borrow value: UniqueInt) -[Echo UniqueInt]> Int\n  let out = Echo.echo(value)\n  case out\n    Unique(v) -> v\n\nfn main() -> Int\n  0\n",
        "kea-cli-borrow-effect-op-consume-rejected",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("passing a borrowed unique parameter to effect op should fail");
    assert!(
        err.contains("borrowed value `value` cannot be consumed"),
        "expected borrow-consumption diagnostic for effect op, got: {err}"
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

    let run =
        run_file(&source_path).expect("auto-borrow inferred call should not consume caller unique");
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
fn compile_rejects_returning_borrow_parameter_through_alias() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\nfn leak_alias(borrow value: Unique Int) -> Unique Int\n  let forwarded = value\n  forwarded\n",
        "kea-cli-borrow-return-alias-escape-rejected",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("returning aliased borrowed parameter should fail");
    assert!(
        err.contains("borrowed value") && err.contains("cannot be consumed"),
        "expected borrow escape diagnostic through alias, got: {err}"
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
fn compile_rejects_capturing_borrow_parameter_through_alias() {
    let source_path = write_temp_source(
        "enum Unique a\n  Unique(a)\n\nfn leak_capture_alias(borrow value: Unique Int) -> fn() -> Int\n  let forwarded = value\n  ||\n    case forwarded\n      Unique(v) -> v\n",
        "kea-cli-borrow-capture-alias-escape-rejected",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("capturing aliased borrowed parameter should fail");
    assert!(
        err.contains("borrowed value") && err.contains("cannot be consumed"),
        "expected borrow capture diagnostic through alias, got: {err}"
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
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_division_by_zero_panics_with_message() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  let x = 10\n  let y = 0\n  x / y\n",
        "kea-cli-div-by-zero",
        "kea",
    );
    let output_path = temp_artifact_path("kea-cli-div-by-zero", "bin");

    let compiled = compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
    link_object_bytes(&compiled.object, &output_path).expect("link should work");

    let output = std::process::Command::new(&output_path)
        .output()
        .expect("aot executable should run");

    assert_eq!(output.status.code(), Some(101));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("panic: integer division by zero"),
        "expected panic message on stderr, got: {stderr}"
    );

    let _ = std::fs::remove_file(source_path);
    let _ = std::fs::remove_file(output_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_and_execute_modulo_by_zero_panics_with_message() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  let x = 10\n  let y = 0\n  x % y\n",
        "kea-cli-mod-by-zero",
        "kea",
    );
    let output_path = temp_artifact_path("kea-cli-mod-by-zero", "bin");

    let compiled = compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
    link_object_bytes(&compiled.object, &output_path).expect("link should work");

    let output = std::process::Command::new(&output_path)
        .output()
        .expect("aot executable should run");

    assert_eq!(output.status.code(), Some(101));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("panic: integer remainder by zero"),
        "expected panic message on stderr, got: {stderr}"
    );

    let _ = std::fs::remove_file(source_path);
    let _ = std::fs::remove_file(output_path);
}

#[test]
fn compile_and_execute_division_nonzero_works() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  100 / 10\n",
        "kea-cli-div-nonzero",
        "kea",
    );

    let run = run_file(&source_path).expect("division run should succeed");
    assert_eq!(run.exit_code, 10);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_mutual_recursion_exit_code() {
    let source_path = write_temp_source(
        "fn is_even(n: Int) -> Int\n  if n == 0\n    1\n  else\n    is_odd(n - 1)\n\nfn is_odd(n: Int) -> Int\n  if n == 0\n    0\n  else\n    is_even(n - 1)\n\nfn main() -> Int\n  is_even(10)\n",
        "kea-cli-mutual-recursion",
        "kea",
    );

    let run = run_file(&source_path).expect("mutual recursion should work");
    assert_eq!(run.exit_code, 1);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_case_match_on_recursive_enum_from_function_return_exit_code() {
    let source_path = write_temp_source(
        "enum Chain\n  End\n  Link(Int, Chain)\n\nfn build(n: Int) -> Chain\n  if n <= 0\n    Chain.End\n  else\n    Chain.Link(n, build(n - 1))\n\nfn is_end(c: Chain) -> Int\n  case c\n    Chain.End -> 1\n    Chain.Link(_, _) -> 0\n\nfn main() -> Int\n  is_end(build(3))\n",
        "kea-cli-recursive-enum-case-from-call",
        "kea",
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_recursive_enum_case_with_step_two_builder_exit_code() {
    let source_path = write_temp_source(
        "enum Chain\n  End\n  Link(Int, Chain)\n\nfn build(n: Int) -> Chain\n  if n <= 0\n    Chain.End\n  else\n    Chain.Link(n, build(n - 2))\n\nfn sum_chain(c: Chain, acc: Int) -> Int\n  case c\n    Chain.End -> acc\n    Chain.Link(v, rest) -> sum_chain(rest, acc + v)\n\nfn main() -> Int\n  sum_chain(build(6), 0)\n",
        "kea-cli-recursive-enum-step-two-case",
        "kea",
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 12);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_recursive_enum_case_with_add_negative_step_builder_exit_code() {
    let source_path = write_temp_source(
        "enum Chain\n  End\n  Link(Int, Chain)\n\nfn build(n: Int) -> Chain\n  if n <= 0\n    Chain.End\n  else\n    Chain.Link(n, build(n + -2))\n\nfn sum_chain(c: Chain, acc: Int) -> Int\n  case c\n    Chain.End -> acc\n    Chain.Link(v, rest) -> sum_chain(rest, acc + v)\n\nfn main() -> Int\n  sum_chain(build(6), 0)\n",
        "kea-cli-recursive-enum-add-negative-step-case",
        "kea",
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 12);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_recursive_enum_case_with_expression_step_and_threshold_exit_code() {
    let source_path = write_temp_source(
        "enum Chain\n  End\n  Link(Int, Chain)\n\nfn build(n: Int) -> Chain\n  if n <= 1 + 1\n    Chain.End\n  else\n    Chain.Link(n, build(n - (1 + 1)))\n\nfn sum_chain(c: Chain, acc: Int) -> Int\n  case c\n    Chain.End -> acc\n    Chain.Link(v, rest) -> sum_chain(rest, acc + v)\n\nfn main() -> Int\n  sum_chain(build(6), 0)\n",
        "kea-cli-recursive-enum-expression-threshold-step-case",
        "kea",
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 10);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_recursive_enum_case_with_pre_call_helper_exit_code() {
    let source_path = write_temp_source(
        "enum Chain\n  End\n  Link(Int, Chain)\n\nfn weight(x: Int) -> Int\n  x + x\n\nfn build(n: Int) -> Chain\n  if n <= 0\n    Chain.End\n  else\n    Chain.Link(weight(n), build(n - 1))\n\nfn sum_chain(c: Chain, acc: Int) -> Int\n  case c\n    Chain.End -> acc\n    Chain.Link(v, rest) -> sum_chain(rest, acc + v)\n\nfn main() -> Int\n  sum_chain(build(3), 0)\n",
        "kea-cli-recursive-enum-pre-call-helper-case",
        "kea",
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 12);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_recursive_enum_case_with_gt_recurse_guard_exit_code() {
    let source_path = write_temp_source(
        "enum Chain\n  End\n  Link(Int, Chain)\n\nfn build(n: Int) -> Chain\n  if n > 0\n    Chain.Link(n, build(n - 1))\n  else\n    Chain.End\n\nfn sum_chain(c: Chain, acc: Int) -> Int\n  case c\n    Chain.End -> acc\n    Chain.Link(v, rest) -> sum_chain(rest, acc + v)\n\nfn main() -> Int\n  sum_chain(build(3), 0)\n",
        "kea-cli-recursive-enum-gt-guard-case",
        "kea",
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 6);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_forward_reference_exit_code() {
    let source_path = write_temp_source(
        "fn caller() -> Int\n  callee(40)\n\nfn callee(x: Int) -> Int\n  x + 2\n\nfn main() -> Int\n  caller()\n",
        "kea-cli-forward-ref",
        "kea",
    );

    let run = run_file(&source_path).expect("forward reference should work");
    assert_eq!(run.exit_code, 42);

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
fn compile_and_execute_float_captured_in_lambda_exit_code() {
    let source_path = write_temp_source(
        "fn apply(f: fn(Float) -> Float, x: Float) -> Float\n  f(x)\n\nfn main() -> Int\n  let offset = 1.5\n  let result = apply(|x| x + offset, 40.0)\n  if result > 41.0\n    42\n  else\n    0\n",
        "kea-cli-float-lambda-capture",
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
fn compile_elides_release_ops_for_value_only_record_churn_program() {
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

    assert_eq!(
        alloc_count, 0,
        "expected value-only record churn to avoid heap allocations, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        release_count, 0,
        "expected value-only record churn to avoid release churn, stats: {:?}",
        compiled.stats
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
    let app_main_stats = compiled
        .stats
        .per_function
        .iter()
        .filter(|f| f.function == "main" || f.function.ends_with(".main"))
        .collect::<Vec<_>>();
    assert!(
        !app_main_stats.is_empty(),
        "expected app main stats to exist, stats: {:?}",
        compiled.stats
    );
    let alloc_count: usize = app_main_stats
        .iter()
        .map(|f| f.alloc_count)
        .sum();
    let main_release_count: usize = app_main_stats
        .iter()
        .map(|f| f.release_count)
        .sum();

    assert_eq!(
        retain_count, 0,
        "expected linear alias ownership transfer to avoid retain churn, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        main_release_count, 0,
        "expected value-only record alias chain to elide release churn in main path, stats: {:?}",
        compiled.stats
    );
    assert_eq!(
        alloc_count, 0,
        "expected value-only record alias chain to avoid heap allocation churn in main path, stats: {:?}",
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
fn compile_and_execute_nested_lambda_returning_lambda_in_local_binding_exit_code() {
    let source_path = write_temp_source(
        "fn outer(a: Int) -> fn(Int) -> Int\n  let make = |b|\n    |c| a + b + c\n  make(30)\n\nfn main() -> Int\n  let f = outer(10)\n  f(2)\n",
        "kea-cli-nested-closure-three-scope-capture",
        "kea",
    );

    let run = run_file(&source_path).expect("nested lambda returning lambda should run");
    assert_eq!(run.exit_code, 42);

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

    let artifact = compile_file(&source_path, CodegenMode::Aot).expect("compile should succeed");
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
fn compile_and_execute_handler_resume_with_closure_capturing_clause_arg_exit_code() {
    let source_path = write_temp_source(
        "effect Factory\n  fn build(seed: Int) -> fn(Int) -> Int\n\nfn program() -[Factory]> fn(Int) -> Int\n  Factory.build(40)\n\nfn main() -> Int\n  let add = handle program()\n    Factory.build(seed) -> resume (|x| x + seed)\n  add(2)\n",
        "kea-cli-handler-resume-closure-captures-clause-arg",
        "kea",
    );

    let run = run_file(&source_path)
        .expect("compiled handler lowering should support effect ops returning closures");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_handler_two_argument_callback_clause_exit_code() {
    let source_path = write_temp_source(
        "effect Math\n  fn add(a: Int, b: Int) -> Int\n\nfn program() -[Math]> Int\n  Math.add(40, 2)\n\nfn main() -> Int\n  handle program()\n    Math.add(a, b) -> resume a + b\n",
        "kea-cli-handler-two-arg-callback-clause",
        "kea",
    );

    let run = run_file(&source_path).expect("two-argument callback handler clause should run");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_reject_handler_callback_clause_non_variable_arg_pattern() {
    let source_path = write_temp_source(
        "effect Math\n  fn add(a: Int, b: Int) -> Int\n\nfn program() -[Math]> Int\n  Math.add(40, 2)\n\nfn main() -> Int\n  handle program()\n    Math.add(40, b) -> resume 40 + b\n",
        "kea-cli-handler-callback-clause-non-var-pattern",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("compiled lowering should reject non-variable callback arg patterns");
    assert!(
        err.contains("requires simple variable argument patterns for callback lowering"),
        "expected callback-pattern lowering diagnostic, got: {err}"
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
fn compile_and_execute_handle_then_clause_case_body_exit_code() {
    let source_path = write_temp_source(
        "effect Reader C\n  fn ask() -> C\n\nfn read() -[Reader Int]> Int\n  Reader.ask()\n\nfn main() -> Int\n  handle read()\n    Reader.ask() -> resume 2\n    then value ->\n      case value\n        2 -> 42\n        _ -> 0\n",
        "kea-cli-handle-then-case-body",
        "kea",
    );

    let run = run_file(&source_path).expect("handle then with case body should run");
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
fn compile_and_execute_nested_same_effect_handlers_three_levels_exit_code() {
    let source_path = write_temp_source(
        "effect Reader C\n  fn ask() -> C\n\nfn inner() -[Reader Int]> Int\n  Reader.ask()\n\nfn middle() -[Reader Int]> Int\n  let a = handle inner()\n    Reader.ask() -> resume 2\n  a + Reader.ask()\n\nfn outer() -[Reader Int]> Int\n  let b = handle middle()\n    Reader.ask() -> resume 20\n  b + Reader.ask()\n\nfn main() -> Int\n  handle outer()\n    Reader.ask() -> resume 200\n",
        "kea-cli-nested-same-effect-handlers-three-levels",
        "kea",
    );

    let run = run_file(&source_path).expect("nested same-effect handlers should run");
    assert_eq!(run.exit_code, 222);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_nested_same_effect_handlers_ten_levels_exit_code() {
    let depth = 10;
    let mut source = String::from(
        "effect Reader C\n  fn ask() -> C\n\nfn level0() -[Reader Int]> Int\n  Reader.ask()\n\n",
    );

    for level in 1..=depth {
        source.push_str(&format!(
                "fn level{level}() -[Reader Int]> Int\n  let inner = handle level{}()\n    Reader.ask() -> resume {level}\n  inner + Reader.ask()\n\n",
                level - 1
            ));
    }

    source.push_str(&format!(
        "fn main() -> Int\n  handle level{depth}()\n    Reader.ask() -> resume {}\n",
        depth + 1
    ));

    let source_path = write_temp_source(
        &source,
        "kea-cli-nested-same-effect-handlers-ten-levels",
        "kea",
    );

    let run = run_file(&source_path).expect("ten-level nested same-effect handlers should run");
    assert_eq!(run.exit_code, 66);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_recursive_handler_installation_depth_exit_code() {
    let source_path = write_temp_source(
        "effect Reader C\n  fn ask() -> C\n\nfn descend(n: Int) -[Reader Int]> Int\n  if n == 0\n    Reader.ask()\n  else\n    let inner = handle descend(n - 1)\n      Reader.ask() -> resume n\n    inner + 1\n\nfn main() -> Int\n  handle descend(25)\n    Reader.ask() -> resume 0\n",
        "kea-cli-recursive-handler-installation-depth",
        "kea",
    );

    let run = run_file(&source_path).expect("recursive handler installation should run");
    assert_eq!(run.exit_code, 26);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn handler_clause_residual_fail_propagates() {
    // A handler clause body that calls Fail.fail should propagate the failure
    // to the outer `catch` via the TLS slot.  The outer catch receives Err.
    let source_path = write_temp_source(
        "effect Echo\n  fn say(s: String) -> Unit\n\neffect Fail E\n  fn fail(error: E) -> Never\n\nfn computation() -[Echo]> Unit\n  Echo.say(\"hello\")\n\nfn main() -> Int\n  let r = catch handle computation()\n    Echo.say(s) ->\n      Fail.fail(\"no says allowed\")\n      resume ()\n  case r\n    Ok(_) -> 0\n    Err(_) -> 42\n",
        "kea-cli-tls-fail-propagates",
        "kea",
    );
    let run = run_file(&source_path)
        .expect("handler_clause_residual_fail_propagates should compile and run");
    assert_eq!(
        run.exit_code, 42,
        "outer catch should receive the callback Fail as Err"
    );
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn handler_clause_residual_fail_not_triggered() {
    // Happy path: callback body has a conditional Fail.fail branch that is
    // statically unreachable (0 == 1).  The TLS wrapping is compiled in
    // because hir_body_has_residual_fail returns true, but at runtime the
    // Fail path is never taken, so the outer catch should see Ok.
    let source_path = write_temp_source(
        "effect Echo\n  fn say(s: String) -> Unit\n\neffect Fail E\n  fn fail(error: E) -> Never\n\nfn computation() -[Echo]> Unit\n  Echo.say(\"hello\")\n\nfn main() -> Int\n  let r = catch handle computation()\n    Echo.say(s) ->\n      if 0 == 1\n        Fail.fail(\"never reached\")\n      else\n        ()\n      resume ()\n  case r\n    Ok(_) -> 42\n    Err(_) -> 0\n",
        "kea-cli-tls-fail-not-triggered",
        "kea",
    );
    let run = run_file(&source_path)
        .expect("handler_clause_residual_fail_not_triggered should compile and run");
    assert_eq!(
        run.exit_code, 42,
        "happy path: TLS slot never written, Ok should be returned"
    );
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn handler_clause_residual_fail_nested() {
    // Nested handlers: inner callback Fails, outer catch receives it.
    // The inner handler's catch intercepts the inner Fail via TLS and
    // the outer handler's catch should NOT see inner Fail (slot is cleared).
    let source_path = write_temp_source(
        "effect Inner\n  fn op() -> Unit\n\neffect Outer\n  fn run() -> Unit\n\neffect Fail E\n  fn fail(error: E) -> Never\n\nfn inner_comp() -[Inner]> Unit\n  Inner.op()\n\nfn main() -> Int\n  let inner_r = catch handle inner_comp()\n    Inner.op() ->\n      Fail.fail(\"inner fail\")\n      resume ()\n  case inner_r\n    Ok(_) -> 0\n    Err(_) -> 42\n",
        "kea-cli-tls-fail-nested",
        "kea",
    );
    let run = run_file(&source_path)
        .expect("handler_clause_residual_fail_nested should compile and run");
    assert_eq!(
        run.exit_code, 42,
        "inner catch should receive the callback Fail from inner handler"
    );
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn handler_clause_residual_fail_multi_yield() {
    // Multi-yield: computation calls the effect operation twice.
    // Both callback invocations attempt to Fail.  First-Fail-wins: the TLS
    // slot is set on the first invocation and the second invocation's payload
    // is dropped (slot already non-null).  The outer catch sees exactly one Err.
    let source_path = write_temp_source(
        "effect Echo\n  fn say(s: String) -> Unit\n\neffect Fail E\n  fn fail(error: E) -> Never\n\nfn computation() -[Echo]> Unit\n  Echo.say(\"first\")\n  Echo.say(\"second\")\n\nfn main() -> Int\n  let r = catch handle computation()\n    Echo.say(s) ->\n      Fail.fail(s)\n      resume ()\n  case r\n    Ok(_) -> 0\n    Err(_) -> 42\n",
        "kea-cli-tls-fail-multi-yield",
        "kea",
    );
    let run = run_file(&source_path)
        .expect("handler_clause_residual_fail_multi_yield should compile and run");
    assert_eq!(
        run.exit_code, 42,
        "outer catch should receive the Fail and first-Fail-wins should prevent double-set"
    );
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_handler_clause_with_direct_fail_call_is_rejected() {
    // Previously rejected; now that TLS propagation is implemented, this
    // should compile and run correctly — the outer catch receives the Fail.
    let source_path = write_temp_source(
        "effect Echo\n  fn say(s: String) -> Unit\n\neffect Fail E\n  fn fail(error: E) -> Never\n\nfn computation() -[Echo]> Int\n  Echo.say(\"hello\")\n  42\n\nfn main() -> Int\n  let r = catch handle computation()\n    Echo.say(s) ->\n      Fail.fail(\"no says allowed\")\n      resume ()\n  case r\n    Ok(v) -> v\n    Err(_) -> 99\n",
        "kea-cli-handler-clause-residual-fail",
        "kea",
    );

    let run = run_file(&source_path)
        .expect("residual Fail in handler clause should now compile and run");
    assert_eq!(
        run.exit_code, 99,
        "outer catch should receive the callback Fail as Err"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_handler_clause_fail_inside_catch_is_allowed() {
    // Fail.fail inside a `catch` within the handler clause body is fine:
    // the catch swallows the failure before it can escape the callback.
    // Echo.say returns Unit so resume must provide Unit; computation returns 42.
    let source_path = write_temp_source(
        "effect Echo\n  fn say(s: String) -> Unit\n\neffect Fail E\n  fn fail(error: E) -> Never\n\nfn computation() -[Echo]> Int\n  Echo.say(\"hello\")\n  42\n\nfn main() -> Int\n  handle computation()\n    Echo.say(s) ->\n      let _ = catch Fail.fail(\"swallowed\")\n      resume ()\n",
        "kea-cli-handler-clause-fail-inside-catch",
        "kea",
    );

    let run = run_file(&source_path).expect("Fail inside catch in handler clause should succeed");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_reject_fail_triggered_after_resume_in_current_lowering() {
    let source_path = write_temp_source(
        "effect Fail\n  fn fail(err: Int) -> Never\n\neffect Gate\n  fn read() -> Int\n\nfn program() -[Gate, Fail Int]> Int\n  let n = Gate.read()\n  if n == 0\n    fail 9\n  else\n    n\n\nfn main() -> Int\n  let r = catch handle program()\n    Gate.read() -> resume 0\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
        "kea-cli-resume-path-fail-caught",
        "kea",
    );

    let err = compile_file(&source_path, CodegenMode::Aot)
        .expect_err("current pipeline should reject this program");
    // The `catch handle program()` composition causes the effect
    // inference to attribute a spurious IO to main (pre-existing
    // inference gap in catch+handle nesting).  The purity check
    // now catches this before lowering gets a chance to run.
    assert!(
        err.contains("declared pure") || err.contains("Fail-only lowering invariant violated"),
        "expected purity or lowering-gap diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_state_put_inside_state_clause_with_side_effects() {
    // State.put handler clause calls State.put(next + 10) before resuming.
    // The side-effecting callback dispatches to the OUTER State handler
    // (captured at callback creation time, before HandlerEnter). This is
    // re-entrant effect dispatch and is now correctly handled via the
    // general callback path with Block-ending-in-Resume classification.
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn probe() -[State Int]> Int\n  State.put(5)\n  0\n\nfn run_inner() -[State Int]> Int\n  handle probe()\n    State.get() -> resume 0\n    State.put(next) ->\n      State.put(next + 10)\n      resume ()\n\nfn main() -> Int\n  handle run_inner()\n    State.get() -> resume 100\n    State.put(next) -> resume ()\n    then value ->\n      State.get()\n",
        "kea-cli-state-put-inside-state-clause-forwards",
        "kea",
    );

    let run = run_file(&source_path)
        .expect("side-effecting state clause should compile");
    assert_eq!(run.exit_code, 15);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_fail_inside_state_does_not_rollback_state_exit_code() {
    let source_path = write_temp_source(
        "effect Fail\n  fn fail(err: Int) -> Never\n\neffect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn boom() -[Fail Int]> Int\n  fail 7\n\nfn run() -[State Int]> Int\n  State.put(5)\n  let result = catch boom()\n  case result\n    Ok(v) -> v\n    Err(e) -> State.get()\n\nfn main() -> Int\n  handle run()\n    State.get() -> resume 0\n    State.put(next) -> resume ()\n",
        "kea-cli-fail-inside-state-no-rollback",
        "kea",
    );

    let run = run_file(&source_path).expect("state should remain updated after local catch");
    assert_eq!(run.exit_code, 5);

    let _ = std::fs::remove_file(source_path);
}

// ── Tier 3: evidence-passing dispatch tests ──────────────────────────

#[test]
fn compile_and_execute_evidence_three_deep_call_chain_exit_code() {
    // handler → fn1 → fn2 → State.get(), evidence threaded through 3 levels
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn level2() -[State Int]> Int\n  State.get()\n\nfn level1() -[State Int]> Int\n  level2() + 1\n\nfn main() -> Int\n  handle level1()\n    State.get() -> resume 41\n    State.put(next) -> resume ()\n",
        "kea-cli-evidence-three-deep",
        "kea",
    );

    let run = run_file(&source_path).expect("evidence threading through 3 levels should work");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_evidence_five_deep_call_chain_exit_code() {
    // handler → fn1 → fn2 → fn3 → fn4 → State.get()
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn d4() -[State Int]> Int\n  State.get()\n\nfn d3() -[State Int]> Int\n  d4()\n\nfn d2() -[State Int]> Int\n  d3()\n\nfn d1() -[State Int]> Int\n  d2()\n\nfn main() -> Int\n  handle d1()\n    State.get() -> resume 42\n    State.put(next) -> resume ()\n",
        "kea-cli-evidence-five-deep",
        "kea",
    );

    let run = run_file(&source_path).expect("evidence threading through 5 levels should work");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_effect_polymorphic_callback_forwards_handler_exit_code() {
    // fn apply takes effectful callback, handler installed by caller
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn apply(f: fn() -[State Int]> Int) -[State Int]> Int\n  f()\n\nfn read_state() -[State Int]> Int\n  State.get()\n\nfn main() -> Int\n  handle apply(read_state)\n    State.get() -> resume 42\n    State.put(next) -> resume ()\n",
        "kea-cli-effect-polymorphic-callback",
        "kea",
    );

    let run = run_file(&source_path).expect("effect polymorphic callback should forward handler");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_effect_polymorphic_callback_with_put_exit_code() {
    // effectful callback that both reads and writes state
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn apply(f: fn() -[State Int]> Int) -[State Int]> Int\n  f()\n\nfn bump_state() -[State Int]> Int\n  let s = State.get()\n  State.put(s + 1)\n  State.get()\n\nfn main() -> Int\n  handle apply(bump_state)\n    State.get() -> resume 41\n    State.put(next) -> resume ()\n",
        "kea-cli-effect-polymorphic-callback-put",
        "kea",
    );

    let run = run_file(&source_path).expect("polymorphic callback with put should work");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_inline_state_handler_get_returns_initial_exit_code() {
    // Inline handler: handle body directly calls State.get() in same function
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn main() -> Int\n  handle State.get()\n    State.get() -> resume 42\n    State.put(next) -> resume ()\n",
        "kea-cli-inline-state-handler",
        "kea",
    );

    let run = run_file(&source_path).expect("inline state handler should work");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_cross_boundary_1arg_unit_non_tail_handler() {
    // Cross-function dispatch: non-stateful 1-arg Unit operation with non-tail resume.
    // Store.save(42) fires in do_save(), handler in main() transforms result with +1.
    // Body returns 100, chain adds 1 → exit 101.
    let source_path = write_temp_source(
        "effect Store\n  fn save(value: Int) -> Unit\n\nfn do_save() -[Store]> Int\n  Store.save(42)\n  100\n\nfn main() -> Int\n  handle do_save()\n    Store.save(v) ->\n      let r = resume ()\n      r + 1\n",
        "kea-cli-cross-boundary-1arg-unit-non-tail",
        "kea",
    );

    let run = run_file(&source_path).expect("cross-boundary 1-arg Unit non-tail should work");
    assert_eq!(run.exit_code, 101);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_state_get_survives_across_handler_boundary() {
    // Regression: state cell must not be freed before handler body executes.
    // The optimizer (schedule_trailing_releases_after_last_use) sees closure
    // init as the last direct use of the state cell. If the cell is in
    // release_cells, it gets freed before the handler body calls State.get().
    // This test catches dangling pointer regressions (was SIGBUS/garbage pre-fix).
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn read_state() -[State Int]> Int\n  State.get()\n\nfn main() -> Int\n  handle read_state()\n    State.get() -> resume 77\n    State.put(next) -> resume ()\n",
        "kea-cli-state-survives-boundary",
        "kea",
    );

    let run = run_file(&source_path).expect("state cell must survive across handler boundary");
    assert_eq!(run.exit_code, 77);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_state_put_then_get_across_boundary() {
    // State.put followed by State.get in a different function.
    // Both callbacks must hold valid references to the same state cell.
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn update_and_read() -[State Int]> Int\n  State.put(99)\n  State.get()\n\nfn main() -> Int\n  handle update_and_read()\n    State.get() -> resume 0\n    State.put(next) -> resume ()\n",
        "kea-cli-state-put-get-boundary",
        "kea",
    );

    let run = run_file(&source_path).expect("put then get across boundary should work");
    assert_eq!(run.exit_code, 99);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_state_multiple_gets_across_boundary() {
    // Multiple State.get() calls across function boundary.
    // State cell must remain valid for all invocations.
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn double_get() -[State Int]> Int\n  let a = State.get()\n  let b = State.get()\n  a + b\n\nfn main() -> Int\n  handle double_get()\n    State.get() -> resume 21\n    State.put(next) -> resume ()\n",
        "kea-cli-state-multi-get-boundary",
        "kea",
    );

    let run = run_file(&source_path).expect("multiple gets across boundary should work");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_state_interleaved_put_get_across_boundary() {
    // Interleaved put/get: put(10), get, put(20), get → should return 20
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn interleave() -[State Int]> Int\n  State.put(10)\n  let _ = State.get()\n  State.put(20)\n  State.get()\n\nfn main() -> Int\n  handle interleave()\n    State.get() -> resume 0\n    State.put(next) -> resume ()\n",
        "kea-cli-state-interleave-boundary",
        "kea",
    );

    let run = run_file(&source_path).expect("interleaved put/get across boundary should work");
    assert_eq!(run.exit_code, 20);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_mixed_dispatch_and_direct_effects_exit_code() {
    // function with both State (dispatch via handler) and IO (direct capability)
    let source_path = write_temp_source(
        "use IO\n\neffect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn compute() -[State Int, IO]> Int\n  IO.stdout(\"hello\")\n  State.get()\n\nfn main() -[IO]> Int\n  handle compute()\n    State.get() -> resume 42\n    State.put(next) -> resume ()\n",
        "kea-cli-mixed-dispatch-and-direct",
        "kea",
    );

    let run = run_file(&source_path).expect("mixed dispatch and direct effects should work");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_nested_evidence_inner_shadows_outer_exit_code() {
    // inner handler provides new evidence for same effect, shadowing outer
    let source_path = write_temp_source(
        "effect Reader C\n  fn ask() -> C\n\nfn inner_read() -[Reader Int]> Int\n  Reader.ask()\n\nfn middle() -[Reader Int]> Int\n  let a = handle inner_read()\n    Reader.ask() -> resume 2\n  a + Reader.ask()\n\nfn main() -> Int\n  handle middle()\n    Reader.ask() -> resume 40\n",
        "kea-cli-nested-evidence-shadows",
        "kea",
    );

    let run = run_file(&source_path).expect("inner handler should shadow outer evidence");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_evidence_through_closure_exit_code() {
    // closure captures evidence from enclosing handler scope
    let source_path = write_temp_source(
        "effect Reader C\n  fn ask() -> C\n\nfn make_and_call() -[Reader Int]> Int\n  let f = || Reader.ask() + 1\n  f()\n\nfn main() -> Int\n  handle make_and_call()\n    Reader.ask() -> resume 41\n",
        "kea-cli-evidence-through-closure",
        "kea",
    );

    let run = run_file(&source_path).expect("closure should capture evidence from handler scope");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_capability_mock_io_stdout_exit_code() {
    // user handler intercepts IO.stdout, proving capability mocking works
    let source_path = write_temp_source(
        // IO.exit is included as a zero-resume clause: Never-returning ops don't call
        // resume — the clause body value becomes the handle expression result directly.
        "use IO\n\nfn program() -[IO]> Int\n  IO.stdout(\"intercepted\")\n  42\n\nfn main() -> Int\n  handle program()\n    IO.stdout(msg) -> resume ()\n    IO.stderr(msg) -> resume ()\n    IO.read_file(path) -> resume \"\"\n    IO.write_file(path, data) -> resume ()\n    IO.file_exists(path) -> resume True\n    IO.env_var(name) -> resume \"\"\n    IO.mkdir(path) -> resume ()\n    IO.exit(code) -> code\n",
        "kea-cli-capability-mock-io-stdout",
        "kea",
    );

    let run = run_file(&source_path).expect("capability mock IO.stdout should work");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

// ── Zero-resume handler clause tests ────────────────────────────────
// Never-returning ops (IO.exit, Fail.fail) can be intercepted by a handler
// clause whose body becomes the result of the handle expression directly —
// no `resume` call, the computation is cut short at the op invocation.

#[test]
fn compile_and_execute_zero_resume_io_exit_intercepted_by_handler() {
    // IO.exit is a Never-returning op; its handler clause body (code) becomes
    // the handle expression result, intercepting the abort and returning 42.
    let source_path = write_temp_source(
        "use IO\n\nfn program() -[IO]> Int\n  IO.exit(42)\n\nfn main() -> Int\n  handle program()\n    IO.exit(code) -> code\n",
        "kea-cli-zero-resume-io-exit",
        "kea",
    );

    let run = run_file(&source_path).expect("zero-resume IO.exit handler should compile and execute");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_zero_resume_normal_completion_path() {
    // When the handled body completes without calling the Never-returning op,
    // the handle expression returns the body's normal result (not the clause body).
    let source_path = write_temp_source(
        "use IO\n\nfn program() -[IO]> Int\n  99\n\nfn main() -> Int\n  handle program()\n    IO.exit(code) -> code\n",
        "kea-cli-zero-resume-normal-completion",
        "kea",
    );

    let run = run_file(&source_path).expect("zero-resume normal completion should work");
    assert_eq!(run.exit_code, 99);

    let _ = std::fs::remove_file(source_path);
}

// ── Tier 4: non-tail-resumptive handler tests ────────────────────────
// Non-tail resume via clause body splitting: `let x = resume val; f(x)`
// splits into a tail-resumptive callback (returns val) + post-resume
// code (f applied to the handle result).

#[test]
fn compile_non_tail_resume_transforms_result() {
    // Zero-arg non-tail resume via callback stacking (pure reader effect)
    // let x = resume 40; x + 2  →  callback returns 40, chain adds 2
    let source_path = write_temp_source(
        "effect Reader C\n  fn ask() -> C\n\nfn body() -[Reader Int]> Int\n  Reader.ask()\n\nfn main() -> Int\n  handle body()\n    Reader.ask() ->\n      let x = resume 40\n      x + 2\n",
        "kea-cli-non-tail-resume-transforms",
        "kea",
    );

    let run = run_file(&source_path).expect("non-tail resume transforms result should run");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_non_tail_resume_with_pre_resume_computation() {
    // Pre-resume computation feeds into resume value (no captures needed)
    // let r = resume (x * 2); r + 1
    let source_path = write_temp_source(
        "effect Transform\n  fn get(x: Int) -> Int\n\nfn body() -[Transform]> Int\n  Transform.get(20)\n\nfn main() -> Int\n  handle body()\n    Transform.get(x) ->\n      let r = resume x * 2\n      r + 2\n",
        "kea-cli-non-tail-resume-pre-resume-comp",
        "kea",
    );

    let run =
        run_file(&source_path).expect("non-tail resume with pre-resume computation should run");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_non_tail_resume_choose_first() {
    // Choose pattern: resume with first option, return the pick
    let source_path = write_temp_source(
        "effect Choose\n  fn choose(n: Int) -> Int\n\nfn body() -[Choose]> Int\n  Choose.choose(100)\n\nfn main() -> Int\n  handle body()\n    Choose.choose(n) ->\n      let picked = resume n\n      picked\n",
        "kea-cli-non-tail-resume-choose-first",
        "kea",
    );

    let run = run_file(&source_path).expect("non-tail resume choose first should run");
    assert_eq!(run.exit_code, 100);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_non_tail_resume_with_then_clause() {
    // Non-tail resume composes with then clause
    // post-resume produces intermediate, then-clause transforms it
    let source_path = write_temp_source(
        "effect Reader C\n  fn ask() -> C\n\nfn body() -[Reader Int]> Int\n  Reader.ask()\n\nfn main() -> Int\n  handle body()\n    Reader.ask() ->\n      let x = resume 40\n      x + 2\n    then result ->\n      result + 100\n",
        "kea-cli-non-tail-resume-then-clause",
        "kea",
    );

    let run = run_file(&source_path).expect("non-tail resume with then clause should run");
    assert_eq!(run.exit_code, 142);

    let _ = std::fs::remove_file(source_path);
}

// ── Callback stacking: multi-yield non-tail handler tests ────────────
// When the same handled operation fires multiple times, callback stacking
// builds a LIFO chain of post-resume transforms. After handle returns,
// the chain unwinds on the body result.

#[test]
fn compile_non_tail_resume_multi_yield_choose() {
    // Choose.choose called twice, `picked * 2` per invocation.
    // Body: choose(10) + choose(20) = 30
    // Chain: identity → wrap(picked*2) → wrap(wrap(picked*2))
    // Unwind: chain(30) = ((30 * 2) * 2) = 120
    let source_path = write_temp_source(
        "effect Choose\n  fn choose(n: Int) -> Int\n\nfn body() -[Choose]> Int\n  let a = Choose.choose(10)\n  let b = Choose.choose(20)\n  a + b\n\nfn main() -> Int\n  handle body()\n    Choose.choose(n) ->\n      let picked = resume n\n      picked * 2\n",
        "kea-cli-non-tail-multi-yield-choose",
        "kea",
    );

    let run = run_file(&source_path).expect("multi-yield choose should run");
    assert_eq!(run.exit_code, 120);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_non_tail_resume_single_yield_with_chain() {
    // Single invocation with chain stacking (non-zero-arg path)
    // Same as choose_first but verifies chain unwind works for single invocation
    // Body: choose(20) = 20
    // Chain: identity → wrap(picked + 1)
    // Unwind: chain(20) = identity(20 + 1) = 21
    let source_path = write_temp_source(
        "effect Choose\n  fn choose(n: Int) -> Int\n\nfn body() -[Choose]> Int\n  Choose.choose(20)\n\nfn main() -> Int\n  handle body()\n    Choose.choose(n) ->\n      let picked = resume n\n      picked + 1\n",
        "kea-cli-non-tail-single-yield-chain",
        "kea",
    );

    let run = run_file(&source_path).expect("single yield with chain should run");
    assert_eq!(run.exit_code, 21);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_non_tail_resume_multi_yield_zero_arg() {
    // Zero-arg multi-yield: Reader.ask called twice with non-tail handler
    // Body: ask() + ask() = 10 + 10 = 20
    // Chain: identity → wrap(x * 3) → wrap(wrap(x * 3))
    // Unwind: chain(20) = ((20 * 3) * 3) = 180
    let source_path = write_temp_source(
        "effect Reader C\n  fn ask() -> C\n\nfn body() -[Reader Int]> Int\n  let a = Reader.ask()\n  let b = Reader.ask()\n  a + b\n\nfn main() -> Int\n  handle body()\n    Reader.ask() ->\n      let x = resume 10\n      x * 3\n",
        "kea-cli-non-tail-multi-yield-zero-arg",
        "kea",
    );

    let run = run_file(&source_path).expect("multi-yield zero-arg should run");
    assert_eq!(run.exit_code, 180);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_non_tail_resume_with_pre_resume_binding_capture() {
    // Pre-resume binding `n` captured in post-resume body via __kea_internal_capture_store.
    // Transform.get(x=10): n = x + 5 = 15, resume 15, body returns 15, r = 15, r + n = 30.
    let source_path = write_temp_source(
        "effect Transform\n  fn get(x: Int) -> Int\n\nfn body() -[Transform]> Int\n  Transform.get(10)\n\nfn main() -> Int\n  handle body()\n    Transform.get(x) ->\n      let n = x + 5\n      let r = resume n\n      r + n\n",
        "kea-cli-non-tail-resume-pre-resume-capture",
        "kea",
    );

    let run = run_file(&source_path).expect("pre-resume binding capture should compile and run");
    assert_eq!(run.exit_code, 30);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_non_tail_resume_with_pre_resume_capture_multi_yield() {
    // Multi-yield: each invocation captures its own snapshot of pre-resume binding `n`.
    // First: Choose.choose(10) → n = 15, resume 15
    // Second: Choose.choose(20) → n = 25, resume 25
    // body = 15 + 25 = 40
    // Chain unwind (LIFO): second's post-resume(40) = 40 + 25 = 65,
    //                       first's post-resume(65) = 65 + 15 = 80
    let source_path = write_temp_source(
        "effect Choose\n  fn choose(x: Int) -> Int\n\nfn body() -[Choose]> Int\n  let a = Choose.choose(10)\n  let b = Choose.choose(20)\n  a + b\n\nfn main() -> Int\n  handle body()\n    Choose.choose(x) ->\n      let n = x + 5\n      let r = resume n\n      r + n\n",
        "kea-cli-non-tail-pre-resume-capture-multi-yield",
        "kea",
    );

    let run = run_file(&source_path).expect("multi-yield pre-resume capture should work");
    assert_eq!(run.exit_code, 80);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_non_tail_resume_clause_arg_and_pre_resume_capture_combined() {
    // Both clause arg capture AND pre-resume binding capture in one handler.
    // Transform.get(x=10): n = x * 2 = 20, resume n = resume 20, body returns 20,
    // r = 20, r + n + x = 20 + 20 + 10 = 50.
    let source_path = write_temp_source(
        "effect Transform\n  fn get(x: Int) -> Int\n\nfn body() -[Transform]> Int\n  Transform.get(10)\n\nfn main() -> Int\n  handle body()\n    Transform.get(x) ->\n      let n = x * 2\n      let r = resume n\n      r + n + x\n",
        "kea-cli-non-tail-clause-arg-and-pre-resume-capture",
        "kea",
    );

    let run = run_file(&source_path).expect("combined clause arg + pre-resume capture should work");
    assert_eq!(run.exit_code, 50);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_pure_function_calling_effectful_forward_reference() {
    // Per KERNEL.md §5.3: `->` asserts empty effects.  `pure` calls `eff`
    // which has `[Reader Int]`, so `pure` transitively performs Reader.
    // The compiler must reject `pure`'s declared `->` signature.
    let source_path = write_temp_source(
        "effect Reader C\n  fn ask() -> C\n\nfn pure(n: Int) -> Int\n  if n == 0\n    0\n  else\n    eff(n - 1)\n\nfn eff(n: Int) -[Reader Int]> Int\n  if n == 0\n    Reader.ask()\n  else\n    pure(n - 1)\n\nfn main() -> Int\n  handle eff(2)\n    Reader.ask() -> resume 7\n",
        "kea-cli-mutual-recursion-pure-effectful-reject",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("pure function calling effectful function must be rejected");
    assert!(
        err.contains("declared pure") && err.contains("effects"),
        "expected purity violation diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_pure_function_directly_calling_effectful() {
    // A pure function directly calling an effectful function must be rejected.
    let source_path = write_temp_source(
        "effect Log\n  fn info(msg: String) -> Unit\n\nfn greet() -[Log]> Unit\n  Log.info(\"hi\")\n\nfn wrapper() -> Unit\n  greet()\n\nfn main() -> Int\n  0\n",
        "kea-cli-pure-calls-effectful-direct",
        "kea",
    );

    let err = run_file(&source_path).expect_err("pure fn calling effectful fn must be rejected");
    assert!(
        err.contains("declared pure") && err.contains("Log"),
        "expected purity violation mentioning Log, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_pure_function_with_handle_covering_all_effects() {
    // A pure function that handles all effects of its callee should pass.
    let source_path = write_temp_source(
        "effect Counter\n  fn next() -> Int\n\nfn count() -[Counter]> Int\n  Counter.next()\n\nfn main() -> Int\n  handle count()\n    Counter.next() -> resume 42\n",
        "kea-cli-pure-handle-all-effects",
        "kea",
    );

    let run = run_file(&source_path).expect("pure fn handling all effects should work");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_higher_order_pure_function_with_callback() {
    // A pure higher-order function with parametric callback effects
    // should not be rejected — the open tail variable is not a
    // concrete effect violation.
    let source_path = write_temp_source(
        "fn apply(f: fn(Int) -> Int, x: Int) -> Int\n  f(x)\n\nfn main() -> Int\n  apply(|x| x + 1, 41)\n",
        "kea-cli-pure-higher-order-callback",
        "kea",
    );

    let run = run_file(&source_path).expect("pure higher-order fn should work");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_function_with_fifty_parameters_exit_code() {
    let mut source = String::from("fn sum50(");
    for i in 1..=50 {
        if i > 1 {
            source.push_str(", ");
        }
        source.push_str(&format!("a{i}: Int"));
    }
    source.push_str(") -> Int\n  ");
    for i in 1..=50 {
        if i > 1 {
            source.push_str(" + ");
        }
        source.push_str(&format!("a{i}"));
    }
    source.push_str("\n\nfn main() -> Int\n  sum50(");
    for i in 1..=50 {
        if i > 1 {
            source.push_str(", ");
        }
        source.push_str(&i.to_string());
    }
    source.push_str(")\n");
    let source_path = write_temp_source(&source, "kea-cli-fifty-parameter-function", "kea");

    let run = run_file(&source_path).expect("50-parameter function run should succeed");
    assert_eq!(run.exit_code, 1275);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_project_with_fifty_parameters_does_not_overflow() {
    let mut source = String::from("fn sum50(");
    for i in 1..=50 {
        if i > 1 {
            source.push_str(", ");
        }
        source.push_str(&format!("a{i}: Int"));
    }
    source.push_str(") -> Int\n  ");
    for i in 1..=50 {
        if i > 1 {
            source.push_str(" + ");
        }
        source.push_str(&format!("a{i}"));
    }
    source.push_str("\n\nfn main() -> Int\n  sum50(");
    for i in 1..=50 {
        if i > 1 {
            source.push_str(", ");
        }
        source.push_str(&i.to_string());
    }
    source.push_str(")\n");
    let source_path = write_temp_source(&source, "kea-cli-fifty-parameter-compile-only", "kea");

    let _ctx = kea::compile_project(&source_path).expect("compile-only should succeed");

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_hundred_nested_let_bindings_exit_code() {
    let mut source = String::from("fn main() -> Int\n");
    for i in 0..100 {
        source.push_str(&format!("  let x{i} = {}\n", i + 1));
    }
    source.push_str("  x99\n");
    let source_path = write_temp_source(&source, "kea-cli-hundred-nested-lets", "kea");

    let run = run_file(&source_path).expect("100 nested let bindings should run");
    assert_eq!(run.exit_code, 100);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_program_with_hundred_top_level_functions_exit_code() {
    let mut source = String::new();
    source.push_str("fn f99(n: Int) -> Int\n  n\n\n");
    for i in (0..99).rev() {
        let next = i + 1;
        source.push_str(&format!("fn f{i}(n: Int) -> Int\n  f{next}(n) + 1\n\n"));
    }
    source.push_str("fn main() -> Int\n  f0(0)\n");

    let source_path = write_temp_source(&source, "kea-cli-hundred-top-level-functions", "kea");

    let run = run_file(&source_path).expect("100 top-level functions should run");
    assert_eq!(run.exit_code, 99);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_program_with_hundred_mutually_recursive_top_level_functions_exit_code() {
    let mut source = String::new();
    for i in 0..100 {
        let next = (i + 1) % 100;
        source.push_str(&format!(
            "fn f{i}(n: Int) -> Int\n  if n == 0\n    {i}\n  else\n    f{next}(n - 1)\n\n"
        ));
    }
    source.push_str("fn main() -> Int\n  f0(100)\n");

    let source_path =
        write_temp_source(&source, "kea-cli-hundred-mutual-top-level-functions", "kea");

    let run =
        run_file(&source_path).expect("100 mutually-recursive top-level functions should run");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_project_accepts_effect_row_with_twenty_effects() {
    let mut source = String::new();
    for i in 1..=20 {
        source.push_str(&format!("effect E{i}\n  fn ping() -> Unit\n\n"));
    }
    source.push_str("fn stress() -[");
    for i in 1..=20 {
        if i > 1 {
            source.push_str(", ");
        }
        source.push_str(&format!("E{i}"));
    }
    source.push_str("]> Int\n  7\n\nfn main() -> Int\n  0\n");

    let source_path = write_temp_source(&source, "kea-cli-effect-row-twenty-effects", "kea");

    let _ctx = kea::compile_project(&source_path)
        .expect("20-effect row compile-only stress should succeed");

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_deeply_nested_option_type_annotation_exit_code() {
    let mut nested = String::from("Int");
    for _ in 0..20 {
        nested = format!("Option({nested})");
    }
    let source = format!(
        "fn main() -> Int\n  let v: {nested} = None\n  case v\n    None -> 1\n    Some(_) -> 0\n"
    );

    let source_path = write_temp_source(&source, "kea-cli-deep-option-type", "kea");

    let run = run_file(&source_path).expect("deep nested option type should run");
    assert_eq!(run.exit_code, 1);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_thousand_line_case_with_five_hundred_variants_exit_code() {
    let mut source = String::from("enum Big\n");
    for i in 0..500 {
        source.push_str(&format!("  V{i}\n"));
    }
    source.push_str("\nfn main() -> Int\n  case V499\n");
    for i in 0..500 {
        source.push_str(&format!("    V{i} -> {i}\n"));
    }

    let source_path = write_temp_source(&source, "kea-cli-large-case-500", "kea");
    let run = run_file(&source_path).expect("500-variant case stress should run");
    assert_eq!(run.exit_code, 499);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_negative_modulo_exit_code() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  -5 % 3\n",
        "kea-cli-negative-modulo",
        "kea",
    );

    let run = run_file(&source_path).expect("negative modulo should run");
    assert_eq!(run.exit_code, -2);

    let _ = std::fs::remove_file(source_path);
}

#[test]
#[cfg(not(target_os = "windows"))]
fn compile_build_and_execute_aot_string_interpolation_with_fifty_expressions_stdout() {
    let mut interpolated = String::new();
    let mut expected = String::new();
    for i in 1..=50 {
        interpolated.push('{');
        interpolated.push_str(&i.to_string());
        interpolated.push('}');
        expected.push_str(&i.to_string());
    }

    let source = format!(
        "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  let s = \"{interpolated}\"\n  IO.stdout(s)\n"
    );
    let source_path = write_temp_source(&source, "kea-cli-string-interpolation-fifty", "kea");
    let output_path = temp_artifact_path("kea-cli-aot-string-interpolation-fifty", "bin");

    let compiled = compile_file(&source_path, CodegenMode::Aot).expect("aot compile should work");
    link_object_bytes(&compiled.object, &output_path).expect("link should work");

    let output = std::process::Command::new(&output_path)
        .output()
        .expect("aot executable should run");
    assert_eq!(output.status.code(), Some(0));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains(&expected),
        "expected stdout to contain interpolated payload, got `{stdout}`"
    );

    let _ = std::fs::remove_file(source_path);
    let _ = std::fs::remove_file(output_path);
}

#[test]
fn compile_and_execute_handler_clause_with_side_effects_before_tail_resume() {
    // Handler clause body with side effects before a tail resume:
    // State.get clause does Log.log(1) then resumes with 0.
    // The callback body should include the side effects (Log.log)
    // and return the resume value (0). Previously rejected as
    // non-tail-resumptive; now correctly handled via the general
    // callback path with Block-ending-in-Resume classification.
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\neffect Log\n  fn log(msg: Int) -> Unit\n\nfn f() -[State Int, Log]> Int\n  State.get()\n\nfn run_state() -[Log]> Int\n  handle f()\n    State.get() ->\n      Log.log(1)\n      resume 0\n    State.put(next) -> resume ()\n\nfn main() -> Int\n  handle run_state()\n    Log.log(msg) -> resume ()\n",
        "kea-cli-handler-side-effects-before-resume",
        "kea",
    );

    let run = run_file(&source_path).expect("run should succeed");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_reject_handler_clause_with_nested_handle_before_resume() {
    let source_path = write_temp_source(
        "effect Reader C\n  fn ask() -> C\n\nfn main() -> Int\n  handle Reader.ask()\n    Reader.ask() ->\n      let inner = handle Reader.ask()\n        Reader.ask() -> resume 2\n      resume inner\n",
        "kea-cli-reject-nested-handle-before-resume",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("run should reject non-tail handler clause with nested handle");
    assert!(
        err.contains("missing active handler cell")
            || err.contains("must be tail-resumptive"),
        "expected rejection for nested-handle clause, got: {err}"
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
fn compile_and_execute_nested_catch_inner_handles_inner_fail_exit_code() {
    let source_path = write_temp_source(
        "effect Fail\n  fn fail(err: Int) -> Never\n\nfn inner() -[Fail Int]> Int\n  fail 3\n\nfn outer() -[Fail Int]> Int\n  let handled = catch inner()\n  let inner_value = case handled\n    Ok(v) -> v\n    Err(e) -> e + 1\n  if inner_value == 4\n    fail 9\n  else\n    0\n\nfn main() -> Int\n  let r = catch outer()\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
        "kea-cli-catch-nested-inner-handles-inner-fail",
        "kea",
    );

    let run = run_file(&source_path).expect("nested catch run should succeed");
    assert_eq!(run.exit_code, 9);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_catch_wraps_handle_result_exit_code() {
    let source_path = write_temp_source(
        "effect Fail\n  fn fail(err: Int) -> Never\n\neffect Reader C\n  fn ask() -> C\n\nfn base() -[Reader Int]> Int\n  Reader.ask()\n\nfn wrapped() -[Fail Int]> Int\n  let x = handle base()\n    Reader.ask() -> resume 2\n  if x == 2\n    fail 7\n  else\n    x\n\nfn main() -> Int\n  let r = catch wrapped()\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
        "kea-cli-catch-wraps-handle-result",
        "kea",
    );

    let run = run_file(&source_path).expect("catch around handle should succeed");
    assert_eq!(run.exit_code, 7);

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
fn compile_rejects_try_sugar_on_non_result_expression() {
    let source_path = write_temp_source(
        "effect Fail\n  fn fail(err: Int) -> Never\n\nfn run() -[Fail Int]> Int\n  42?\n\nfn main() -> Int\n  let r = catch run()\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
        "kea-cli-try-sugar-non-result",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject ? on non-Result");
    // With Result as a sum type, ? on Int produces "unreachable arm" warnings for Ok/Err
    // (the Int type has no Ok/Err variants) plus a non-exhaustive error.
    assert!(
        err.contains("unreachable constructor arm") || err.contains("non-exhaustive"),
        "expected ? on non-Result to be rejected, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_try_sugar_when_error_type_mismatches_fail_effect() {
    let source_path = write_temp_source(
        "effect Fail\n  fn fail(err: String) -> Never\n\nfn step(ok: Bool) -> Result(Int, Int)\n  if ok then Ok(41) else Err(7)\n\nfn run(ok: Bool) -[Fail String]> Int\n  step(ok)?\n\nfn main() -> Int\n  let r = catch run(false)\n  case r\n    Ok(v) -> v\n    Err(e) -> 0\n",
        "kea-cli-try-sugar-error-type-mismatch",
        "kea",
    );

    let err = run_file(&source_path)
        .expect_err("run should reject try-sugar when Result error type mismatches Fail effect");
    assert!(
        err.contains("type mismatch") && err.contains("Int") && err.contains("String"),
        "expected try-sugar error-type mismatch diagnostic, got: {err}"
    );

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
fn compile_and_execute_fail_in_handler_then_clause_with_outer_catch_exit_code() {
    let source_path = write_temp_source(
        "effect Fail\n  fn fail(err: Int) -> Never\n\neffect Reader C\n  fn ask() -> C\n\nfn read() -[Reader Int]> Int\n  Reader.ask()\n\nfn main() -> Int\n  let r = catch handle read()\n    Reader.ask() -> resume 1\n    then value ->\n      fail 9\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
        "kea-cli-handler-then-fail-propagates-to-catch",
        "kea",
    );

    let run = run_file(&source_path).expect("fail in handler then should be caught");
    assert_eq!(run.exit_code, 9);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_catch_with_wrong_error_type_annotation() {
    let source_path = write_temp_source(
        "effect Fail\n  fn fail(err: Int) -> Never\n\nfn main() -> Int\n  let r: Result(Int, String) = catch fail 7\n  case r\n    Ok(v) -> v\n    Err(e) -> 0\n",
        "kea-cli-catch-wrong-error-annotation",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject catch error type mismatch");
    assert!(
        err.contains("type annotation mismatch")
            && err.contains("declared `String`")
            && err.contains("type `Int`"),
        "expected catch error type-mismatch diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_catch_direct_fail_exit_code() {
    let source_path = write_temp_source(
        "effect Fail\n  fn fail(err: Int) -> Never\n\nfn main() -> Int\n  let r = catch fail 7\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n",
        "kea-cli-catch-direct-fail",
        "kea",
    );

    let run = run_file(&source_path).expect("direct catch fail should succeed");
    assert_eq!(run.exit_code, 7);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_cyclic_alias_definitions() {
    let source_path = write_temp_source(
        "alias A = B\nalias B = A\n\nfn main() -> Int\n  0\n",
        "kea-cli-alias-cycle",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject cyclic aliases");
    assert!(
        err.contains("cyclic alias definition"),
        "expected cyclic-alias diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_type_annotation_arity_mismatch() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  let v: Result(Int) = Ok(1)\n  0\n",
        "kea-cli-type-arity-mismatch",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject type annotation arity mismatch");
    assert!(
        err.contains("expects 2 type arguments")
            || (err.contains("Result") && err.contains("2") && err.contains("1")),
        "expected type annotation arity mismatch diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_named_record_field_type_mismatch_with_field_context() {
    let source_path = write_temp_source(
        "struct User\n  age: Int\n\nfn main() -> Int\n  let _ = User { age: \"oops\" }\n  0\n",
        "kea-cli-record-field-type-mismatch",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject mismatched record field type");
    assert!(
        (err.contains("field `age` has type") || err.contains("field age has type"))
            && err.contains("Int")
            && err.contains("String"),
        "expected record field type-mismatch diagnostic, got: {err}"
    );
    assert!(
        err.contains("age"),
        "expected mismatched field name in diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_row_polymorphic_argument_missing_required_field() {
    let source_path = write_temp_source(
        "fn get_age(u: { age: Int | r }) -> Int\n  u.age\n\nfn main() -> Int\n  get_age(#{ score: 1 })\n",
        "kea-cli-row-poly-missing-field",
        "kea",
    );

    let err =
        run_file(&source_path).expect_err("run should reject row-polymorphic call missing field");
    assert!(
        err.contains("age")
            && (err.contains("field") || err.contains("type mismatch") || err.contains("record")),
        "expected missing-field context in row-polymorphic diagnostic, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_rejects_function_call_with_too_many_arguments() {
    let source_path = write_temp_source(
        "fn add(x: Int, y: Int) -> Int\n  x + y\n\nfn main() -> Int\n  add(1, 2, 3)\n",
        "kea-cli-call-too-many-args",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject extra positional argument");
    assert!(
        err.contains("too many arguments") || (err.contains("expected 2") && err.contains("got 3")),
        "expected arity mismatch diagnostic with expected/got counts, got: {err}"
    );

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_type_errors_do_not_expose_internal_inference_variables() {
    let source_path = write_temp_source(
        "fn get_age(u: { age: Int | r }) -> Int\n  u.age\n\nfn main() -> Int\n  get_age(#{ age: \"oops\" })\n",
        "kea-cli-no-internal-type-vars-in-errors",
        "kea",
    );

    let err = run_file(&source_path).expect_err("run should reject row-polymorphic type mismatch");
    assert!(
        (err.contains("type mismatch") || err.contains("field `age` has type"))
            && err.contains("Int")
            && err.contains("String"),
        "expected a user-facing type mismatch diagnostic, got: {err}"
    );
    assert!(
        !err.contains("?t") && !err.contains("TypeVarId"),
        "diagnostic leaked internal type variables, got: {err}"
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
fn compile_and_execute_receiver_placeholder_in_qualified_call_exit_code() {
    // fold(init, list, f) with receiver placement: list.fold(init, _, f)
    let source = concat!(
        "fn fold(init: Int, list: Int, f: fn(Int, Int) -> Int) -> Int\n",
        "  f(init, list)\n",
        "\n",
        "fn main() -> Int\n",
        "  let x = 21\n",
        "  x.fold(21, _, |a, b| a + b)\n",
    );
    let source_path =
        write_temp_source(source, "kea-cli-receiver-placeholder-qualified", "kea");

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

#[test]
fn compile_and_execute_float_in_handler_callback() {
    // Verify that concrete Float types are threaded through handler callback
    // closures. The handler clause receives a Float arg and resumes with it.
    // Previously, Float args were erased to Dynamic (I64) which would cause
    // wrong register class at the Cranelift ABI level.
    let source_path = write_temp_source(
        "effect FloatEff\n  fn send(value: Float) -> Unit\n\nfn do_send() -[FloatEff]> Int\n  FloatEff.send(3.14)\n  42\n\nfn main() -> Int\n  handle do_send()\n    FloatEff.send(value) -> resume ()\n",
        "kea-cli-float-handler-callback",
        "kea",
    );

    let run = run_file(&source_path).expect("float handler callback should compile and run");
    assert_eq!(run.exit_code, 42);

    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_float_state_handler() {
    // Float state type threaded through State effect handler.
    // State.get() returns Float, State.put() accepts Float.
    let source_path = write_temp_source(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn use_state() -[State Float]> Float\n  let x = State.get()\n  State.put(x)\n  State.get()\n\nfn main() -> Int\n  handle use_state()\n    State.get() -> resume 2.71\n    State.put(next) -> resume ()\n  0\n",
        "kea-cli-float-state-handler",
        "kea",
    );

    let run = run_file(&source_path).expect("float state handler should compile and run");
    assert_eq!(run.exit_code, 0);

    let _ = std::fs::remove_file(source_path);
}

// --- kea check tests ---

#[test]
fn parse_check_command_with_file() {
    let args = vec![
        "kea".to_string(),
        "check".to_string(),
        "main.kea".to_string(),
    ];
    let command = parse_cli(&args).expect("cli parse should succeed");
    assert_eq!(
        command,
        Command::Check {
            input: Some(PathBuf::from("main.kea")),
        }
    );
}

#[test]
fn parse_check_command_without_file() {
    let args = vec!["kea".to_string(), "check".to_string()];
    let command = parse_cli(&args).expect("cli parse should succeed");
    assert_eq!(command, Command::Check { input: None });
}

#[test]
fn parse_check_rejects_extra_args() {
    let args = vec![
        "kea".to_string(),
        "check".to_string(),
        "a.kea".to_string(),
        "b.kea".to_string(),
    ];
    let err = parse_cli(&args).expect_err("extra args should be rejected");
    assert!(
        err.contains("unexpected arguments for `check`"),
        "expected extra-args error, got: {err}"
    );
}

#[test]
fn check_file_succeeds_on_valid_source() {
    let source_path = write_temp_source("fn main() -> Int\n  42\n", "kea-check-valid", "kea");
    let result = check_file(&source_path).expect("check should succeed on valid source");
    assert!(!result.has_errors, "valid source should produce no errors");
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn check_file_does_not_execute_the_program() {
    // A program that returns exit code 99. kea check should succeed (exit 0),
    // not run the program. We verify by asserting check_file returns Ok and the
    // result has no errors — not that the exit code is 99.
    let source_path = write_temp_source(
        "fn main() -> Int\n  99\n",
        "kea-check-no-exec",
        "kea",
    );
    let result = check_file(&source_path).expect("check should succeed without executing");
    assert!(!result.has_errors, "valid source should produce no errors");
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn check_file_accepts_library_without_main() {
    // Modules without a main function are valid targets for kea check.
    let source_path = write_temp_source(
        "pub fn double(x: Int) -> Int\n  x * 2\n",
        "kea-check-no-main",
        "kea",
    );
    let result = check_file(&source_path).expect("library module should check successfully");
    assert!(
        !result.has_errors,
        "library without main should produce no errors"
    );
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn check_file_reports_type_error() {
    // Type mismatch: main declared to return Int but returns a Bool.
    // compile_project surfaces type errors as Err(String), so check_file returns Err.
    let source_path = write_temp_source(
        "fn main() -> Int\n  true\n",
        "kea-check-type-error",
        "kea",
    );
    let err = check_file(&source_path).expect_err("type error should cause check_file to return Err");
    assert!(
        err.contains("type annotation mismatch") || err.contains("type inference failed"),
        "error message should describe the type error, got: {err}"
    );
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn check_file_reports_parse_error() {
    // Truncated return type — parse error, not a type error.
    let source_path = write_temp_source(
        "fn main() ->\n",
        "kea-check-parse-error",
        "kea",
    );
    let err = check_file(&source_path).expect_err("parse error should cause check_file to return Err");
    assert!(
        err.contains("parsing failed") || err.contains("expected"),
        "error message should describe the parse error, got: {err}"
    );
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn check_file_reports_undefined_variable() {
    let source_path = write_temp_source(
        "fn main() -> Int\n  undefined_var\n",
        "kea-check-undefined-var",
        "kea",
    );
    let err = check_file(&source_path).expect_err("undefined variable should cause check_file to return Err");
    assert!(
        err.contains("undefined variable") || err.contains("undefined_var"),
        "error message should name the undefined variable, got: {err}"
    );
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn check_file_resolves_cross_module_imports() {
    let project_dir = temp_project_dir("kea-check-multi-module");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    std::fs::write(src_dir.join("math.kea"), "pub fn double(x: Int) -> Int\n  x * 2\n")
        .expect("math module write should succeed");
    let app_path = src_dir.join("app.kea");
    std::fs::write(&app_path, "use Math\nfn main() -> Int\n  Math.double(21)\n")
        .expect("app module write should succeed");

    let result = check_file(&app_path).expect("multi-module check should succeed");
    assert!(
        !result.has_errors,
        "multi-module project with correct types should produce no errors"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

#[test]
fn check_file_catches_cross_module_type_error() {
    let project_dir = temp_project_dir("kea-check-multi-module-type-error");
    let src_dir = project_dir.join("src");
    std::fs::create_dir_all(&src_dir).expect("source dir should be created");

    std::fs::write(src_dir.join("math.kea"), "pub fn double(x: Int) -> Int\n  x * 2\n")
        .expect("math module write should succeed");
    // Pass a Bool where Int is expected
    let app_path = src_dir.join("app.kea");
    std::fs::write(&app_path, "use Math\nfn main() -> Int\n  Math.double(true)\n")
        .expect("app module write should succeed");

    let err = check_file(&app_path)
        .expect_err("cross-module type error should cause check_file to return Err");
    assert!(
        err.contains("type") || err.contains("inference"),
        "error message should describe a type mismatch, got: {err}"
    );

    let _ = std::fs::remove_dir_all(project_dir);
}

// ---------------------------------------------------------------------------
// Tests: nominal block methods (struct/enum inline fn, §2.8 / §3.5 / §11.6)
// ---------------------------------------------------------------------------

#[test]
fn struct_inline_method_ums_dispatch() {
    // struct with fn inside its block; called via UMS and qualified form.
    let source = concat!(
        "use Test\n",
        "\n",
        "struct Point\n",
        "  x: Int\n",
        "  y: Int\n",
        "\n",
        "  fn distance(_ self: Point, _ other: Point) -> Int\n",
        "    let dx = self.x - other.x\n",
        "    let dy = self.y - other.y\n",
        "    dx * dx + dy * dy\n",
        "\n",
        "  fn origin() -> Point\n",
        "    Point { x: 0, y: 0 }\n",
        "\n",
        "test \"struct block method UMS\"\n",
        "  let p = Point { x: 3, y: 4 }\n",
        "  let q = Point.origin()\n",
        "  Test.assert(p.distance(q) == 25)\n",
        "  Test.assert(Point.distance(p, q) == 25)\n",
        "\n",
        "test \"struct block static method\"\n",
        "  let o = Point.origin()\n",
        "  Test.assert(o.x == 0)\n",
        "  Test.assert(o.y == 0)\n",
    );
    let path = write_temp_source(source, "kea-struct-inline-method", "kea");
    let run = run_test_file(&path).expect("struct inline method test should pass");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(
        failures.is_empty(),
        "struct inline method failures: {failures:?}"
    );
    let _ = std::fs::remove_file(path);
}

#[test]
fn enum_inline_associated_method() {
    // enum with an associated (static) fn inside its block.
    let source = concat!(
        "use List\n",
        "use Test\n",
        "\n",
        "enum Direction\n",
        "  North\n",
        "  South\n",
        "  East\n",
        "  West\n",
        "\n",
        "  fn all() -> List Direction\n",
        "    Cons(North, Cons(South, Cons(East, Cons(West, Nil))))\n",
        "\n",
        "test \"enum block associated method\"\n",
        "  let dirs = Direction.all()\n",
        "  Test.assert(List.length(dirs) == 4)\n",
    );
    let path = write_temp_source(source, "kea-enum-inline-static", "kea");
    let run = run_test_file(&path).expect("enum inline associated method test should pass");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(
        failures.is_empty(),
        "enum inline associated method failures: {failures:?}"
    );
    let _ = std::fs::remove_file(path);
}

#[test]
fn enum_inline_receiver_method() {
    // enum with a receiver fn inside its block; called via UMS and qualified form.
    let source = concat!(
        "use Test\n",
        "\n",
        "@derive(Eq)\n",
        "enum Direction\n",
        "  North\n",
        "  South\n",
        "  East\n",
        "  West\n",
        "\n",
        "  fn opposite(_ self: Direction) -> Direction\n",
        "    case self\n",
        "      North -> South\n",
        "      South -> North\n",
        "      East  -> West\n",
        "      West  -> East\n",
        "\n",
        "test \"enum block receiver method UMS\"\n",
        "  let n = North\n",
        "  Test.assert(n.opposite() == South)\n",
        "  Test.assert(Direction.opposite(East) == West)\n",
    );
    let path = write_temp_source(source, "kea-enum-inline-receiver", "kea");
    let run = run_test_file(&path).expect("enum inline receiver method test should pass");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(
        failures.is_empty(),
        "enum inline receiver method failures: {failures:?}"
    );
    let _ = std::fs::remove_file(path);
}

#[test]
fn struct_inline_method_coexists_with_file_scope_fn() {
    // A struct can have block methods while the same file has unrelated
    // file-scope functions. No collision if the names are different.
    let source = concat!(
        "use Test\n",
        "\n",
        "struct Vec2\n",
        "  x: Int\n",
        "  y: Int\n",
        "\n",
        "  fn magnitude_sq(_ self: Vec2) -> Int\n",
        "    self.x * self.x + self.y * self.y\n",
        "\n",
        "fn scale(_ v: Vec2, _ factor: Int) -> Vec2\n",
        "  Vec2 { x: v.x * factor, y: v.y * factor }\n",
        "\n",
        "test \"struct block and file-scope coexist\"\n",
        "  let v = Vec2 { x: 3, y: 4 }\n",
        "  let w = scale(v, 2)\n",
        "  Test.assert(v.magnitude_sq() == 25)\n",
        "  Test.assert(w.magnitude_sq() == 100)\n",
    );
    let path = write_temp_source(source, "kea-struct-inline-plus-file-scope", "kea");
    let run = run_test_file(&path).expect("struct inline + file-scope test should pass");
    let failures: Vec<_> = run.cases.iter().filter(|c| !c.passed).collect();
    assert!(
        failures.is_empty(),
        "struct inline + file-scope failures: {failures:?}"
    );
    let _ = std::fs::remove_file(path);
}

#[test]
fn enum_block_duplicate_method_is_rejected() {
    // Duplicate method name inside a single enum block must error.
    let source = concat!(
        "enum Coin\n",
        "  Heads\n",
        "  Tails\n",
        "\n",
        "  fn flip(_ self: Coin) -> Coin\n",
        "    case self\n",
        "      Heads -> Tails\n",
        "      Tails -> Heads\n",
        "\n",
        "  fn flip(_ self: Coin) -> Coin\n",
        "    Heads\n",
        "\n",
        "fn main() -> Int\n",
        "  0\n",
    );
    let path = write_temp_source(source, "kea-enum-duplicate-method", "kea");
    let err = run_file(&path).expect_err("duplicate method in enum block should fail");
    assert!(
        err.contains("duplicate method") || err.contains("flip"),
        "expected duplicate method error, got: {err}"
    );
    let _ = std::fs::remove_file(path);
}

#[test]
fn merged_namespace_method_vs_file_scope_collision_is_rejected() {
    // In a same-name merge file (struct/enum name == module struct name),
    // a type-block method and a file-scope function with the same name must error.
    // The file must be named "box.kea" so the module struct name is "Box",
    // matching the struct inside → triggering same-name merge collision detection.
    let source = concat!(
        "struct Box\n",
        "  value: Int\n",
        "\n",
        "  fn unwrap(_ self: Box) -> Int\n",
        "    self.value\n",
        "\n",
        "fn unwrap(_ b: Box) -> Int\n",
        "  b.value + 1\n",
        "\n",
        "fn main() -> Int\n",
        "  0\n",
    );
    let dir = temp_project_dir("kea-merged-ns-collision");
    let path = dir.join("box.kea");
    std::fs::write(&path, source).expect("temp source write should succeed");
    let err = run_file(&path).expect_err("merged namespace method collision should fail");
    assert!(
        err.contains("conflict") || err.contains("collision") || err.contains("unwrap"),
        "expected collision error, got: {err}"
    );
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn compile_and_execute_gadt_eval_monomorphic_exit_code() {
    // A simple monomorphic GADT: Expr Int with constructor return type annotations.
    // eval_int : Expr Int -> Int dispatches on the GADT constructor.
    let source = concat!(
        "enum Expr T\n",
        "  IntLit(value: Int) : Expr Int\n",
        "  Add(left: Expr Int, right: Expr Int) : Expr Int\n",
        "\n",
        "fn eval_int(e: Expr Int) -> Int\n",
        "  case e\n",
        "    IntLit(v) -> v\n",
        "    Add(l, r) -> eval_int(l) + eval_int(r)\n",
        "\n",
        "fn main() -> Int\n",
        "  eval_int(Add(IntLit(20), IntLit(22)))\n",
    );
    let source_path = write_temp_source(source, "kea-gadt-eval-mono", "kea");
    let run = run_file(&source_path).expect("GADT monomorphic eval should compile and run");
    assert_eq!(run.exit_code, 42);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_gadt_branch_local_refinement_exit_code() {
    // GADT with both IntLit and BoolLit; eval functions are type-specific.
    // Tests that the GADT where-constraints are branch-local (IntLit arm knows v: Int,
    // BoolLit arm knows v: Bool, and the information doesn't cross arm boundaries).
    // Avoids `then`/`else` as field names since they're reserved keywords.
    let source = concat!(
        "enum Expr T\n",
        "  IntLit(value: Int) : Expr Int\n",
        "  BoolLit(value: Bool) : Expr Bool\n",
        "  Add(left: Expr Int, right: Expr Int) : Expr Int\n",
        "  Cond(guard: Expr Bool, tru: Expr Int, fal: Expr Int) : Expr Int\n",
        "\n",
        "fn eval_int(e: Expr Int) -> Int\n",
        "  case e\n",
        "    IntLit(value: v) -> v\n",
        "    Add(left: l, right: r) -> eval_int(l) + eval_int(r)\n",
        "    Cond(guard: g, tru: t, fal: f) -> if eval_bool(g) then eval_int(t) else eval_int(f)\n",
        "\n",
        "fn eval_bool(e: Expr Bool) -> Bool\n",
        "  case e\n",
        "    BoolLit(value: v) -> v\n",
        "\n",
        "fn main() -> Int\n",
        "  eval_int(Cond(guard: BoolLit(value: true), tru: IntLit(value: 42), fal: IntLit(value: 0)))\n",
    );
    let source_path = write_temp_source(source, "kea-gadt-branch-local", "kea");
    let run = run_file(&source_path).expect("GADT branch-local refinement should compile and run");
    assert_eq!(run.exit_code, 42);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_generic_eq_via_monomorphization_exit_code() {
    // Step 5 verification: generic == works via monomorphization.
    // The monomorphize pass specializes `contains` for each concrete type,
    // so evidence threading for Eq is handled automatically.
    let source = concat!(
        "fn contains(list: List a, x: a) -> Bool where a: Eq\n",
        "  case list\n",
        "    [] -> false\n",
        "    [h, ..t] -> Eq.eq(h, x) or contains(t, x)\n",
        "\n",
        "fn main() -> Int\n",
        "  if contains([1, 2, 3], 2) and not contains([1, 2, 3], 4) then 42 else 0\n",
    );
    let source_path = write_temp_source(source, "kea-generic-eq", "kea");
    let run = run_file(&source_path)
        .expect("generic Eq via monomorphization should compile and run");
    assert_eq!(run.exit_code, 42);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_supertrait_dispatch_exit_code() {
    // Step 3 verification: supertrait methods are available when a supertrait bound is in scope.
    // `Ord` declares `compare`; we use a generic function bounded on `Ord` which transitively
    // requires `Eq`. The solver must check supertrait obligations when resolving `Ord`.
    let source = concat!(
        "fn max_of(a: a, b: a) -> a where a: Ord\n",
        "  case Ord.compare(a, b)\n",
        "    Less -> b\n",
        "    _ -> a\n",
        "\n",
        "fn main() -> Int\n",
        "  max_of(37, 42)\n",
    );
    let source_path = write_temp_source(source, "kea-supertrait", "kea");
    let run = run_file(&source_path)
        .expect("supertrait dispatch should compile and run");
    assert_eq!(run.exit_code, 42);
    let _ = std::fs::remove_file(source_path);
}

#[test]
fn compile_and_execute_associated_type_via_foldable_exit_code() {
    // Step 3 verification: associated types work end-to-end.
    // Define a Wrap trait with associated type Inner, implement for a struct,
    // use it generically to access the associated type.
    let source = concat!(
        "trait Wrap\n",
        "  type Inner\n",
        "  fn unwrap(_ self: Self) -> Int\n",
        "\n",
        "struct MyBox\n",
        "  value: Int\n",
        "\n",
        "MyBox as Wrap where Inner = Int\n",
        "  fn unwrap(_ self: MyBox) -> Int\n",
        "    self.value\n",
        "\n",
        "fn main() -> Int\n",
        "  let b = MyBox { value: 42 }\n",
        "  Wrap.unwrap(b)\n",
    );
    let source_path = write_temp_source(source, "kea-assoc-type", "kea");
    let run = run_file(&source_path)
        .expect("associated type impl should compile and run");
    assert_eq!(run.exit_code, 42);
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

/// Regression test: process_module_in_env (the MCP code path) must not
/// produce type errors for parameterized effect handler clauses.
#[test]
fn process_module_in_env_accepts_parameterized_effect_handler() {
    let source = "effect Reader C\n  fn ask() -> C\n\nfn read() -[Reader Int]> Int\n  Reader.ask()\n\nfn main() -> Int\n  handle read()\n    Reader.ask() -> resume 42\n";
    let (tokens, warnings) = kea_syntax::lex_layout(source, kea_ast::FileId(0))
        .expect("lex should succeed");
    let module = kea_syntax::parse_module(tokens, kea_ast::FileId(0))
        .expect("parse should succeed");

    use kea_infer::typeck::{TypeEnv, RecordRegistry, TraitRegistry, SumTypeRegistry};
    let mut env = TypeEnv::new();
    let mut records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let mut sum_types = SumTypeRegistry::new();

    let result = kea::process_module_in_env(
        &module,
        &mut env,
        &mut records,
        &mut traits,
        &mut sum_types,
        warnings,
    );
    match result {
        Ok(processed) => {
            let errors: Vec<_> = processed
                .diagnostics
                .iter()
                .filter(|d| d.severity == kea_diag::Severity::Error)
                .collect();
            assert!(
                errors.is_empty(),
                "process_module_in_env should produce no errors for valid Reader handler, got: {errors:?}"
            );
        }
        Err(diags) => {
            panic!(
                "process_module_in_env should not fail for valid Reader handler, got: {diags:?}"
            );
        }
    }
}

/// Regression test: process_module_in_env must preserve unsafe-call gating
/// across incremental session modules.
#[test]
fn process_module_in_env_enforces_unsafe_call_gating_across_session_modules() {
    use kea_infer::typeck::{RecordRegistry, SumTypeRegistry, TraitRegistry, TypeEnv};

    fn parse_module_for_test(source: &str, file: u32) -> (kea_ast::Module, Vec<kea_diag::Diagnostic>) {
        let (tokens, warnings) =
            kea_syntax::lex_layout(source, kea_ast::FileId(file)).expect("lex should succeed");
        let module =
            kea_syntax::parse_module(tokens, kea_ast::FileId(file)).expect("parse should succeed");
        (module, warnings)
    }

    let mut env = TypeEnv::new();
    let mut records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let mut sum_types = SumTypeRegistry::new();

    let (unsafe_mod, warnings0) =
        parse_module_for_test("@unsafe\nfn raw_add_one(x: Int) -> Int\n  x + 1\n", 10);
    let registered = kea::process_module_in_env(
        &unsafe_mod,
        &mut env,
        &mut records,
        &mut traits,
        &mut sum_types,
        warnings0,
    )
    .expect("unsafe declaration module should register successfully");
    assert!(
        registered
            .diagnostics
            .iter()
            .all(|d| d.severity != kea_diag::Severity::Error),
        "unsafe declaration module should not produce errors"
    );

    let (safe_caller_mod, warnings1) =
        parse_module_for_test("fn caller() -> Int\n  raw_add_one(1)\n", 11);
    let err = kea::process_module_in_env(
        &safe_caller_mod,
        &mut env,
        &mut records,
        &mut traits,
        &mut sum_types,
        warnings1,
    )
    .expect_err("safe caller should be rejected when calling @unsafe callee in session env");
    assert!(
        err.iter().any(|diag| diag.message.contains(
            "call to `@unsafe` function `raw_add_one` requires unsafe context"
        )),
        "expected unsafe call-site diagnostic, got: {err:?}"
    );

    let (unsafe_block_caller_mod, warnings2) = parse_module_for_test(
        "fn caller_safe() -> Int\n  unsafe\n    raw_add_one(41)\n",
        12,
    );
    let allowed = kea::process_module_in_env(
        &unsafe_block_caller_mod,
        &mut env,
        &mut records,
        &mut traits,
        &mut sum_types,
        warnings2,
    )
    .expect("unsafe block caller should be accepted in session env");
    assert!(
        allowed
            .diagnostics
            .iter()
            .all(|d| d.severity != kea_diag::Severity::Error),
        "unsafe block caller should not produce errors: {:?}",
        allowed.diagnostics
    );
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
