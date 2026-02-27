use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command as ProcessCommand;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use kea_ast::{DeclKind, ExprDecl, FileId, FnDecl, Module, TypeDef};
use kea_codegen::{
    Backend, BackendConfig, CodegenMode, CraneliftBackend, default_abi_manifest,
    execute_hir_main_jit,
};
use kea_diag::{Diagnostic, Severity};
use kea_hir::lower_module;
use kea_infer::typeck::{
    RecordRegistry, SumTypeRegistry, TraitRegistry, TypeEnv, apply_where_clause,
    infer_and_resolve_in_context, infer_fn_decl_effect_row, register_effect_decl,
    register_fn_effect_signature, register_fn_signature, seed_fn_where_type_params_in_context,
    validate_declared_fn_effect_row_with_env_and_records, validate_module_annotations,
    validate_module_fn_annotations, validate_where_clause_traits,
};
use kea_infer::{Category, InferenceContext};
use kea_mir::lower_hir_module;
use kea_syntax::{lex_layout, parse_module};

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

#[derive(Debug)]
struct CompileResult {
    object: Vec<u8>,
    diagnostics: Vec<Diagnostic>,
}

#[derive(Debug)]
struct RunResult {
    exit_code: i32,
    diagnostics: Vec<Diagnostic>,
}

fn compile_file(input: &Path, mode: CodegenMode) -> Result<CompileResult, String> {
    let source = fs::read_to_string(input)
        .map_err(|err| format!("failed to read `{}`: {err}", input.display()))?;

    let pipeline = parse_and_typecheck_module(&source, FileId(0))?;
    let hir = lower_module(&pipeline.module, &pipeline.type_env);
    let mir = lower_hir_module(&hir);
    let abi = default_abi_manifest(&mir);

    let backend = CraneliftBackend;
    let artifact = backend
        .compile_module(
            &mir,
            &abi,
            &BackendConfig {
                mode,
                ..BackendConfig::default()
            },
        )
        .map_err(|err| format!("codegen failed: {err}"))?;

    Ok(CompileResult {
        object: artifact.object,
        diagnostics: pipeline.diagnostics,
    })
}

fn run_file(input: &Path) -> Result<RunResult, String> {
    let source = fs::read_to_string(input)
        .map_err(|err| format!("failed to read `{}`: {err}", input.display()))?;

    let pipeline = parse_and_typecheck_module(&source, FileId(0))?;
    let hir = lower_module(&pipeline.module, &pipeline.type_env);
    let exit_code = execute_hir_main_jit(&hir, &BackendConfig::default())
        .map_err(|err| format!("codegen failed: {err}"))?;

    Ok(RunResult {
        exit_code,
        diagnostics: pipeline.diagnostics,
    })
}

#[derive(Debug)]
struct PipelineResult {
    module: Module,
    type_env: TypeEnv,
    diagnostics: Vec<Diagnostic>,
}

fn parse_and_typecheck_module(source: &str, file_id: FileId) -> Result<PipelineResult, String> {
    let (tokens, mut diagnostics) =
        lex_layout(source, file_id).map_err(|diags| format_diagnostics("lexing failed", &diags))?;

    let module = parse_module(tokens, file_id)
        .map_err(|diags| format_diagnostics("parsing failed", &diags))?;

    let mut env = TypeEnv::new();
    let mut records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let mut sum_types = SumTypeRegistry::new();

    diagnostics.extend(validate_module_fn_annotations(&module));
    diagnostics.extend(validate_module_annotations(&module));
    if has_errors(&diagnostics) {
        return Err(format_diagnostics(
            "type annotation validation failed",
            &diagnostics,
        ));
    }

    register_top_level_declarations(
        &module,
        &mut env,
        &mut records,
        &mut traits,
        &mut sum_types,
        &mut diagnostics,
    )?;

    typecheck_functions(
        &module,
        &mut env,
        &mut records,
        &mut traits,
        &mut sum_types,
        &mut diagnostics,
    )?;

    Ok(PipelineResult {
        module,
        type_env: env,
        diagnostics,
    })
}

fn register_top_level_declarations(
    module: &Module,
    env: &mut TypeEnv,
    records: &mut RecordRegistry,
    traits: &mut TraitRegistry,
    sum_types: &mut SumTypeRegistry,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<(), String> {
    let type_defs: Vec<&TypeDef> = module
        .declarations
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::TypeDef(def) => Some(def),
            _ => None,
        })
        .collect();

    if let Err(diag) = sum_types.register_many(&type_defs, records) {
        diagnostics.push(diag);
        return Err(format_diagnostics(
            "sum type registration failed",
            diagnostics,
        ));
    }

    for decl in &module.declarations {
        match &decl.node {
            DeclKind::AliasDecl(alias) => {
                if let Err(diag) = records.register_alias(alias) {
                    diagnostics.push(diag);
                    return Err(format_diagnostics("alias registration failed", diagnostics));
                }
            }
            DeclKind::OpaqueTypeDef(opaque) => {
                if let Err(diag) = records.register_opaque(opaque) {
                    diagnostics.push(diag);
                    return Err(format_diagnostics(
                        "opaque registration failed",
                        diagnostics,
                    ));
                }
            }
            DeclKind::RecordDef(record) => {
                if let Err(diag) = records.register(record) {
                    diagnostics.push(diag);
                    return Err(format_diagnostics(
                        "record registration failed",
                        diagnostics,
                    ));
                }
            }
            DeclKind::TraitDef(trait_def) => {
                if let Err(diag) = traits.register_trait(trait_def, records) {
                    diagnostics.push(diag);
                    return Err(format_diagnostics("trait registration failed", diagnostics));
                }
            }
            DeclKind::ImplBlock(impl_block) => {
                if let Err(diag) = traits.register_trait_impl(impl_block) {
                    diagnostics.push(diag);
                    return Err(format_diagnostics("impl registration failed", diagnostics));
                }
            }
            DeclKind::EffectDecl(effect_decl) => {
                let effect_diags = register_effect_decl(effect_decl, records, Some(sum_types), env);
                diagnostics.extend(effect_diags);
                if has_errors(diagnostics) {
                    return Err(format_diagnostics(
                        "effect registration failed",
                        diagnostics,
                    ));
                }
            }
            DeclKind::Import(import) => {
                diagnostics.push(
                    Diagnostic::warning(
                        Category::TypeError,
                        format!(
                            "import `{}` is parsed but module resolution is not yet wired in `kea` CLI",
                            import.module.node
                        ),
                    )
                    .at(kea_diag::SourceLocation {
                        file_id: import.module.span.file.0,
                        start: import.module.span.start,
                        end: import.module.span.end,
                    }),
                );
            }
            _ => {}
        }
    }

    Ok(())
}

fn typecheck_functions(
    module: &Module,
    env: &mut TypeEnv,
    records: &mut RecordRegistry,
    traits: &mut TraitRegistry,
    sum_types: &mut SumTypeRegistry,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<(), String> {
    for decl in &module.declarations {
        let fn_decl = match &decl.node {
            DeclKind::Function(fn_decl) => fn_decl.clone(),
            DeclKind::ExprFn(expr_decl) => expr_decl_to_fn_decl(expr_decl),
            _ => continue,
        };

        let where_diags = validate_where_clause_traits(&fn_decl.where_clause, traits);
        diagnostics.extend(where_diags.iter().filter(|d| !is_error(d)).cloned());
        if where_diags.iter().any(is_error) {
            diagnostics.extend(where_diags);
            return Err(format_diagnostics(
                "where-clause validation failed",
                diagnostics,
            ));
        }

        let mut ctx = InferenceContext::new();
        seed_fn_where_type_params_in_context(&fn_decl, traits, &mut ctx);
        let expr = fn_decl.to_let_expr();
        let _ = infer_and_resolve_in_context(&expr, env, &mut ctx, records, traits, sum_types);

        if ctx.has_errors() {
            diagnostics.extend_from_slice(ctx.errors());
            return Err(format_diagnostics("type inference failed", diagnostics));
        }

        ctx.check_trait_bounds(traits);
        if ctx.has_errors() {
            diagnostics.extend_from_slice(ctx.errors());
            return Err(format_diagnostics("trait obligations failed", diagnostics));
        }

        diagnostics.extend(ctx.errors().iter().filter(|d| !is_error(d)).cloned());

        if !fn_decl.where_clause.is_empty()
            && let Some(scheme) = env.lookup(&fn_decl.name.node).cloned()
        {
            let mut scheme = scheme;
            apply_where_clause(&mut scheme, &fn_decl, ctx.substitution());
            env.bind(fn_decl.name.node.clone(), scheme);
        }

        let inferred_effect_row = infer_fn_decl_effect_row(&fn_decl, env);
        if let Err(diag) = validate_declared_fn_effect_row_with_env_and_records(
            &fn_decl,
            &inferred_effect_row,
            env,
            records,
        ) {
            diagnostics.push(diag);
            return Err(format_diagnostics("effect contract failed", diagnostics));
        }

        register_fn_effect_signature(&fn_decl, env);
        let runtime_effect_row = env
            .function_effect_signature(&fn_decl.name.node)
            .map(|sig| sig.effect_row.clone())
            .unwrap_or(inferred_effect_row);
        env.set_function_effect_row(fn_decl.name.node.clone(), runtime_effect_row);
        register_fn_signature(&fn_decl, env);
    }

    Ok(())
}

fn expr_decl_to_fn_decl(expr: &ExprDecl) -> FnDecl {
    FnDecl {
        public: expr.public,
        name: expr.name.clone(),
        doc: expr.doc.clone(),
        annotations: expr.annotations.clone(),
        params: expr.params.clone(),
        return_annotation: expr.return_annotation.clone(),
        effect_annotation: expr.effect_annotation.clone(),
        body: expr.body.clone(),
        testing: expr.testing.clone(),
        testing_tags: expr.testing_tags.clone(),
        span: expr.span,
        where_clause: expr.where_clause.clone(),
    }
}

fn has_errors(diags: &[Diagnostic]) -> bool {
    diags.iter().any(is_error)
}

fn is_error(diag: &Diagnostic) -> bool {
    matches!(diag.severity, Severity::Error)
}

fn emit_diagnostics(diags: &[Diagnostic]) {
    for diag in diags {
        eprintln!("{diag}");
    }
}

fn format_diagnostics(prefix: &str, diagnostics: &[Diagnostic]) -> String {
    if diagnostics.is_empty() {
        return prefix.to_string();
    }

    let rendered = diagnostics
        .iter()
        .map(|d| format!("  - {d}"))
        .collect::<Vec<_>>()
        .join("\n");
    format!("{prefix}:\n{rendered}")
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
    fn compile_and_execute_io_stdout_unit_main_exit_code() {
        let source_path = write_temp_source(
            "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO::stdout(\"hello world\")\n",
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
            "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO::stdout(\"hello \" ++ \"world\")\n",
            "kea-cli-io-stdout-concat",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 0);

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
    fn compile_build_and_execute_aot_io_stdout_unit_main_exit_code() {
        let source_path = write_temp_source(
            "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO::stdout(\"hello aot\")\n",
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
            "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn main() -[IO]> Unit\n  IO::stdout(\"hello \" ++ \"aot\")\n",
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
    fn compile_and_execute_escaping_capturing_lambda_value_is_rejected() {
        let source_path = write_temp_source(
            "fn apply(f: fn(Int) -> Int, x: Int) -> Int\n  f(x)\n\nfn make_adder(y: Int) -> fn(Int) -> Int\n  |x| -> x + y\n\nfn main() -> Int\n  apply(make_adder(2), 40)\n",
            "kea-cli-escaping-capturing-lambda",
            "kea",
        );

        let err = run_file(&source_path).expect_err("run should reject escaping capturing closure value");
        assert!(
            err.contains("capturing closure values currently require immediate or let-bound invocation"),
            "expected unsupported closure-value diagnostic, got: {err}"
        );

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
    fn compile_and_execute_anon_record_pattern_case_exit_code() {
        let source_path = write_temp_source(
            "record User\n  age: Int\n  score: Int\n\nfn main() -> Int\n  let user = User { age: 4, score: 9 }\n  case user\n    #{ age: 4, .. } -> 6\n    _ -> 2\n",
            "kea-cli-anon-record-pattern-case",
            "kea",
        );

        let run = run_file(&source_path).expect("run should succeed");
        assert_eq!(run.exit_code, 6);

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
