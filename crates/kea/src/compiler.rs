use std::any::Any;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use crate::package::{dependency_namespaces, resolve_graph_for_entry, resolve_graph_for_test_entry};

use kea_ast::{
    Annotation, Argument, DeclKind, Expr, ExprDecl, ExprKind, FileId, FnDecl, ImportItems,
    Module, PatternKind, RecordDef, Span, Spanned, TestDecl, TypeAnnotation, TypeDef, VariantField,
    collect_pattern_bindings_pub,
};
use kea_codegen::{
    Backend, BackendConfig, CodegenMode, CraneliftBackend, PassStats, collect_pass_stats,
    default_abi_manifest, execute_hir_main_jit,
};
use kea_diag::{Diagnostic, Severity, SourceLocation};
use kea_hir::{
    HirDecl, HirExpr, HirExprKind, HirFunction, HirModule, check_unique_moves_with_borrow_map,
    collect_borrow_param_positions, infer_auto_borrow_param_positions, lower_module,
};
use kea_infer::typeck::{
    RecordRegistry, SumTypeRegistry, TraitRegistry, TypeEnv, apply_where_clause,
    check_expr_in_context, concrete_method_types_from_decls, infer_and_resolve_in_context,
    register_builtin_int_bitwise_methods, register_builtin_ptr_ops, register_effect_decl,
    register_fn_signature, resolve_annotation, seed_fn_where_type_params_in_context,
    validate_module_annotations,
    validate_module_fn_annotations, validate_where_clause_traits,
};
use kea_infer::{Category, InferenceContext, Reason};
use kea_mir::{MirLoweringConfig, lower_hir_module_with_config};
use kea_syntax::{lex_layout, parse_module};
use kea_types::{
    EffectRow, Type, TypeScheme, free_dim_vars, free_row_vars, free_type_vars,
    sanitize_type_display,
};

const COMPILER_WORKER_STACK_BYTES: usize = 16 * 1024 * 1024;

#[derive(Debug)]
pub struct CompilationContext {
    pub module: Module,
    pub hir: HirModule,
    pub type_env: TypeEnv,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug)]
pub struct CompileResult {
    pub object: Vec<u8>,
    pub stats: PassStats,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug)]
pub struct RunResult {
    pub exit_code: i32,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, Clone)]
pub struct TestCaseResult {
    pub name: String,
    pub passed: bool,
    pub iterations: usize,
    pub diagnostics: Vec<Diagnostic>,
    pub error: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TestRunResult {
    pub cases: Vec<TestCaseResult>,
}

#[derive(Debug, Clone)]
pub struct ModuleBinding {
    pub name: String,
    pub kind: String,
    pub ty: String,
}

#[derive(Debug, Clone)]
pub struct ModuleProcessResult {
    pub bindings: Vec<ModuleBinding>,
    pub diagnostics: Vec<Diagnostic>,
}

/// Return type of `typecheck_functions`: resolved expr-type map + trait-dispatch callee rewrites.
type TypecheckResult = (
    std::collections::BTreeMap<Span, Type>,
    std::collections::BTreeMap<Span, String>,
);

fn span_to_loc(span: Span) -> SourceLocation {
    SourceLocation {
        file_id: span.file.0,
        start: span.start,
        end: span.end,
    }
}

pub fn compile_module(source: &str, file_id: FileId) -> Result<CompilationContext, String> {
    let source_owned = source.to_string();
    run_on_compiler_stack("compile_module", move || {
        compile_module_inner(&source_owned, file_id)
    })
}

fn compile_module_inner(source: &str, file_id: FileId) -> Result<CompilationContext, String> {
    let (tokens, mut diagnostics) =
        lex_layout(source, file_id).map_err(|diags| format_diagnostics("lexing failed", &diags))?;

    let parsed_module = parse_module(tokens, file_id)
        .map_err(|diags| format_diagnostics("parsing failed", &diags))?;
    let module = prepare_module_for_compilation(&parsed_module, &mut diagnostics);

    let mut env = TypeEnv::new();
    register_builtin_int_bitwise_methods(&mut env);
    register_builtin_ptr_ops(&mut env);
    let mut records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let mut sum_types = SumTypeRegistry::new();

    diagnostics.extend(validate_module_fn_annotations(&module));
    diagnostics.extend(validate_module_annotations(&module));
    diagnostics.extend(validate_unsafe_call_sites(&module, None, None, None));
    warn_missing_module_doc(&module, &mut diagnostics);
    if has_errors(&diagnostics) {
        return Err(format_diagnostics(
            "type annotation validation failed",
            &diagnostics,
        ));
    }

    let (module, block_method_owners) = lift_type_block_methods(&module);
    register_top_level_declarations(
        &module,
        &mut env,
        &mut records,
        &mut traits,
        &mut sum_types,
        &mut diagnostics,
        None,
    )?;

    let (expr_types, resolved_trait_callees) = typecheck_functions(
        &module,
        &mut env,
        &mut records,
        &mut traits,
        &mut sum_types,
        &mut diagnostics,
        None,
        &block_method_owners,
    )?;

    let hir = lower_module(&module, &env, &expr_types, &resolved_trait_callees);
    let hir = kea_hir::monomorphize::monomorphize(&hir);
    let explicit_borrow_param_map = collect_borrow_param_positions(&module, None);
    let borrow_param_map = infer_auto_borrow_param_positions(&hir, &explicit_borrow_param_map);
    diagnostics.extend(check_unique_moves_with_borrow_map(&hir, &borrow_param_map));
    if has_errors(&diagnostics) {
        return Err(format_diagnostics("move checking failed", &diagnostics));
    }
    diagnostics.extend(validate_fip_annotations(&module, &hir));
    if has_errors(&diagnostics) {
        return Err(format_diagnostics(
            "`@fip` verification failed",
            &diagnostics,
        ));
    }

    Ok(CompilationContext {
        module,
        hir,
        type_env: env,
        diagnostics,
    })
}

pub fn compile_project(entry: &Path) -> Result<CompilationContext, String> {
    let entry = entry.to_path_buf();
    run_on_compiler_stack("compile_project", move || {
        parse_and_typecheck_project(&entry)
    })
}

pub fn emit_object(ctx: &CompilationContext, mode: CodegenMode) -> Result<CompileResult, String> {
    let hir = ctx.hir.clone();
    let module = ctx.module.clone();
    let diagnostics = ctx.diagnostics.clone();
    run_on_compiler_stack("emit_object", move || {
        let lowering_config = match mode {
            CodegenMode::Jit => MirLoweringConfig::jit(),
            CodegenMode::Aot => MirLoweringConfig::aot(),
        };
        let mir = lower_hir_module_with_config(&hir, &lowering_config);
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
            .map_err(|err| format_codegen_error_with_fip_context(&module, &format!("{err}")))?;

        Ok(CompileResult {
            object: artifact.object,
            stats: artifact.stats,
            diagnostics,
        })
    })
}

pub fn execute_jit(ctx: &CompilationContext) -> Result<RunResult, String> {
    let hir = ctx.hir.clone();
    let module = ctx.module.clone();
    let diagnostics = ctx.diagnostics.clone();
    run_on_compiler_stack("execute_jit", move || {
        let exit_code = execute_hir_main_jit(&hir, &BackendConfig::default())
            .map_err(|err| format_codegen_error_with_fip_context(&module, &format!("{err}")))?;

        Ok(RunResult {
            exit_code,
            diagnostics,
        })
    })
}

fn format_codegen_error_with_fip_context(module: &Module, backend_error: &str) -> String {
    let mut message = format!("codegen failed: {backend_error}");
    if backend_error.contains("unresolved qualified call target") {
        let fip_functions = collect_fip_annotated_function_names(module);
        if !fip_functions.is_empty() {
            message.push_str(
                "\nnote: `@fip` ownership verification succeeded before backend lowering; this unresolved qualified target is a backend/module-lowering gap.",
            );
            message.push_str(&format!(
                "\nnote: verified `@fip` function(s): {}",
                fip_functions.join(", ")
            ));
        }
    }
    message
}

fn collect_fip_annotated_function_names(module: &Module) -> Vec<String> {
    let mut names = Vec::new();
    for decl in &module.declarations {
        match &decl.node {
            DeclKind::Function(fn_decl)
                if fn_decl.annotations.iter().any(|ann| ann.name.node == "fip") =>
            {
                names.push(fn_decl.name.node.clone());
            }
            DeclKind::ExprFn(expr_decl)
                if expr_decl
                    .annotations
                    .iter()
                    .any(|ann| ann.name.node == "fip") =>
            {
                names.push(expr_decl.name.node.clone());
            }
            _ => {}
        }
    }
    names
}

fn has_annotation_named(annotations: &[kea_ast::Annotation], name: &str) -> bool {
    annotations.iter().any(|ann| ann.name.node == name)
}

fn collect_unsafe_annotated_function_names(module: &Module) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for decl in &module.declarations {
        match &decl.node {
            DeclKind::Function(fn_decl) if has_annotation_named(&fn_decl.annotations, "unsafe") => {
                names.insert(fn_decl.name.node.clone());
            }
            DeclKind::ExprFn(expr_decl)
                if has_annotation_named(&expr_decl.annotations, "unsafe") =>
            {
                names.insert(expr_decl.name.node.clone());
            }
            _ => {}
        }
    }
    names
}

fn builtin_unsafe_call_names() -> BTreeSet<String> {
    [
        "Ptr.null",
        "Ptr.read",
        "Ptr.write",
        "Ptr.offset",
        "Ptr.cast",
        "Ptr.alloc",
        "Ptr.free",
        "Kea.Ptr.null",
        "Kea.Ptr.read",
        "Kea.Ptr.write",
        "Kea.Ptr.offset",
        "Kea.Ptr.cast",
        "Kea.Ptr.alloc",
        "Kea.Ptr.free",
    ]
    .into_iter()
    .map(|name| name.to_string())
    .collect()
}

fn collect_unsafe_function_registry(
    loaded_modules: &[LoadedModule],
) -> BTreeMap<String, BTreeSet<String>> {
    let mut registry = BTreeMap::new();
    for loaded in loaded_modules {
        registry.insert(
            loaded.module_path.clone(),
            collect_unsafe_annotated_function_names(&loaded.module),
        );
    }
    registry
}

fn collect_unsafe_call_targets(
    module: &Module,
    module_path: Option<&str>,
    unsafe_registry: Option<&BTreeMap<String, BTreeSet<String>>>,
    ambient_unsafe_names: Option<&BTreeSet<String>>,
) -> BTreeSet<String> {
    let mut unsafe_callees = collect_unsafe_annotated_function_names(module);
    unsafe_callees.extend(builtin_unsafe_call_names());
    if let Some(ambient_unsafe_names) = ambient_unsafe_names {
        unsafe_callees.extend(ambient_unsafe_names.iter().cloned());
    }

    if let Some(module_path) = module_path {
        for name in collect_unsafe_annotated_function_names(module) {
            unsafe_callees.insert(format!("{module_path}.{name}"));
        }
    }

    let Some(unsafe_registry) = unsafe_registry else {
        return unsafe_callees;
    };

    // Fully qualified project names remain valid call targets for unsafe checks.
    for (known_module, items) in unsafe_registry {
        for item in items {
            unsafe_callees.insert(format!("{known_module}.{item}"));
        }
    }

    // Imported module aliases (`use Mod`, `use Mod as Alias`) should preserve
    // unsafe gating on qualified calls (Alias.fn()).
    let import_aliases = collect_import_aliases(module);
    for (alias, imported_module) in &import_aliases {
        if let Some(items) = unsafe_registry.get(imported_module) {
            for item in items {
                unsafe_callees.insert(format!("{alias}.{item}"));
            }
        }
    }

    // Named imports (`use Mod.{fn}`) should also gate bare calls (`fn()`).
    for decl in &module.declarations {
        let DeclKind::Import(import) = &decl.node else {
            continue;
        };
        let ImportItems::Named(items) = &import.items else {
            continue;
        };
        let Some(unsafe_items) = unsafe_registry.get(&import.module.node) else {
            continue;
        };
        for item in items {
            if unsafe_items.contains(&item.node) {
                unsafe_callees.insert(item.node.clone());
            }
        }
    }

    unsafe_callees
}

fn ast_callable_name(expr: &Expr) -> Option<String> {
    match &expr.node {
        ExprKind::Var(name) => Some(name.clone()),
        ExprKind::FieldAccess { expr, field } => {
            let owner = ast_callable_name(expr)?;
            Some(format!("{owner}.{}", field.node))
        }
        _ => None,
    }
}

fn collect_unsafe_call_site_diagnostics_in_expr(
    expr: &Expr,
    unsafe_callees: &BTreeSet<String>,
    in_unsafe_context: bool,
    caller_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match &expr.node {
        ExprKind::Call { func, args } => {
            if !in_unsafe_context
                && let Some(callee_name) = ast_callable_name(func)
                && unsafe_callees.contains(&callee_name)
            {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!(
                            "call to `@unsafe` function `{callee_name}` requires unsafe context"
                        ),
                    )
                    .at(span_to_source_location(expr.span))
                    .with_help(format!(
                        "enclosing function `{caller_name}` is safe; wrap this call in `unsafe` or mark the enclosing function `@unsafe`."
                    )),
                );
            }
            collect_unsafe_call_site_diagnostics_in_expr(
                func,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            for arg in args {
                collect_unsafe_call_site_diagnostics_in_expr(
                    &arg.value,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::Let { value, .. } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                value,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::Lambda { body, .. } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                body,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::Unsafe { body } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                body,
                unsafe_callees,
                true,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                condition,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            collect_unsafe_call_site_diagnostics_in_expr(
                then_branch,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            if let Some(else_branch) = else_branch {
                collect_unsafe_call_site_diagnostics_in_expr(
                    else_branch,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::Case { scrutinee, arms } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                scrutinee,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_unsafe_call_site_diagnostics_in_expr(
                        guard,
                        unsafe_callees,
                        in_unsafe_context,
                        caller_name,
                        diagnostics,
                    );
                }
                collect_unsafe_call_site_diagnostics_in_expr(
                    &arm.body,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::Cond { arms } => {
            for arm in arms {
                collect_unsafe_call_site_diagnostics_in_expr(
                    &arm.condition,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
                collect_unsafe_call_site_diagnostics_in_expr(
                    &arm.body,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::For(for_expr) => {
            collect_unsafe_call_site_diagnostics_in_expr(
                &for_expr.source,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            collect_unsafe_call_site_diagnostics_in_expr(
                &for_expr.body,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::With { call, body, .. } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                call,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            collect_unsafe_call_site_diagnostics_in_expr(
                body,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::Handle {
            expr,
            clauses,
            then_clause,
        } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                expr,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            for clause in clauses {
                collect_unsafe_call_site_diagnostics_in_expr(
                    &clause.body,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
            if let Some(then_clause) = then_clause {
                collect_unsafe_call_site_diagnostics_in_expr(
                    then_clause,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::Resume { value } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                value,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::BinaryOp { left, right, .. } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                left,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            collect_unsafe_call_site_diagnostics_in_expr(
                right,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::UnaryOp { operand, .. } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                operand,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::WhenGuard { body, condition } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                body,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            collect_unsafe_call_site_diagnostics_in_expr(
                condition,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::Range { start, end, .. } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                start,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            collect_unsafe_call_site_diagnostics_in_expr(
                end,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::As { expr, .. } | ExprKind::FieldAccess { expr, .. } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                expr,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::Tuple(items) | ExprKind::List(items) | ExprKind::Block(items) => {
            for item in items {
                collect_unsafe_call_site_diagnostics_in_expr(
                    item,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::Record { fields, spread, .. } | ExprKind::AnonRecord { fields, spread } => {
            for (_, value) in fields {
                collect_unsafe_call_site_diagnostics_in_expr(
                    value,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
            if let Some(spread) = spread {
                collect_unsafe_call_site_diagnostics_in_expr(
                    spread,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::Update { base, fields } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                base,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            for (_, value) in fields {
                collect_unsafe_call_site_diagnostics_in_expr(
                    value,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::Constructor { args, .. } => {
            for arg in args {
                collect_unsafe_call_site_diagnostics_in_expr(
                    &arg.value,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::StringInterp(parts) => {
            for part in parts {
                if let kea_ast::StringInterpPart::Expr(expr) = part {
                    collect_unsafe_call_site_diagnostics_in_expr(
                        expr,
                        unsafe_callees,
                        in_unsafe_context,
                        caller_name,
                        diagnostics,
                    );
                }
            }
        }
        ExprKind::MapLiteral(entries) => {
            for (key, value) in entries {
                collect_unsafe_call_site_diagnostics_in_expr(
                    key,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
                collect_unsafe_call_site_diagnostics_in_expr(
                    value,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::Yield { value } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                value,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::ActorSend { actor, args, .. } | ExprKind::ActorCall { actor, args, .. } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                actor,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            for arg in args {
                collect_unsafe_call_site_diagnostics_in_expr(
                    arg,
                    unsafe_callees,
                    in_unsafe_context,
                    caller_name,
                    diagnostics,
                );
            }
        }
        ExprKind::ControlSend { actor, signal } => {
            collect_unsafe_call_site_diagnostics_in_expr(
                actor,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
            collect_unsafe_call_site_diagnostics_in_expr(
                signal,
                unsafe_callees,
                in_unsafe_context,
                caller_name,
                diagnostics,
            );
        }
        ExprKind::Lit(_)
        | ExprKind::Var(_)
        | ExprKind::None
        | ExprKind::Atom(_)
        | ExprKind::Wildcard => {}
    }
}

fn validate_unsafe_call_sites(
    module: &Module,
    module_path: Option<&str>,
    unsafe_registry: Option<&BTreeMap<String, BTreeSet<String>>>,
    ambient_unsafe_names: Option<&BTreeSet<String>>,
) -> Vec<Diagnostic> {
    let unsafe_callees = collect_unsafe_call_targets(
        module,
        module_path,
        unsafe_registry,
        ambient_unsafe_names,
    );
    if unsafe_callees.is_empty() {
        return Vec::new();
    }

    let mut diagnostics = Vec::new();
    for decl in &module.declarations {
        match &decl.node {
            DeclKind::Function(fn_decl) => {
                let in_unsafe_context = has_annotation_named(&fn_decl.annotations, "unsafe");
                collect_unsafe_call_site_diagnostics_in_expr(
                    &fn_decl.body,
                    &unsafe_callees,
                    in_unsafe_context,
                    &fn_decl.name.node,
                    &mut diagnostics,
                );
            }
            DeclKind::ExprFn(expr_decl) => {
                let in_unsafe_context = has_annotation_named(&expr_decl.annotations, "unsafe");
                collect_unsafe_call_site_diagnostics_in_expr(
                    &expr_decl.body,
                    &unsafe_callees,
                    in_unsafe_context,
                    &expr_decl.name.node,
                    &mut diagnostics,
                );
            }
            _ => {}
        }
    }

    diagnostics
}

pub fn compile_file(input: &Path, mode: CodegenMode) -> Result<CompileResult, String> {
    let ctx = compile_project(input)?;
    emit_object(&ctx, mode)
}

pub fn run_file(input: &Path) -> Result<RunResult, String> {
    let ctx = compile_project(input)?;
    execute_jit(&ctx)
}

#[derive(Debug)]
pub struct CheckResult {
    pub diagnostics: Vec<Diagnostic>,
    pub has_errors: bool,
}

pub fn check_file(input: &Path) -> Result<CheckResult, String> {
    let ctx = compile_project(input)?;
    let errors = has_errors(&ctx.diagnostics);
    Ok(CheckResult {
        diagnostics: ctx.diagnostics,
        has_errors: errors,
    })
}

pub fn run_test_file(input: &Path) -> Result<TestRunResult, String> {
    let loaded_modules = collect_project_modules_for_tests(input)?;
    let entry_module_path = module_path_from_entry(input);
    let Some(entry_module) = loaded_modules
        .iter()
        .find(|module| module.module_path == entry_module_path)
    else {
        return Err(format!(
            "entry module `{entry_module_path}` was not found during test discovery"
        ));
    };

    let (prepared_entry_module, tests) = strip_test_decls_for_runner(&entry_module.module);
    if tests.is_empty() {
        return Ok(TestRunResult { cases: Vec::new() });
    }

    let prepared_modules = loaded_modules
        .into_iter()
        .map(|loaded| {
            if loaded.module_path == entry_module_path {
                LoadedModule {
                    module: prepared_entry_module.clone(),
                    ..loaded
                }
            } else {
                loaded
            }
        })
        .collect::<Vec<_>>();

    let mut results = Vec::with_capacity(tests.len());
    for test in tests {
        let mut scenario_modules = prepared_modules.clone();
        let scenario_entry = scenario_modules
            .iter_mut()
            .find(|module| module.module_path == entry_module_path)
            .ok_or_else(|| {
                format!("entry module `{entry_module_path}` is missing in test scenario")
            })?;

        scenario_entry
            .module
            .declarations
            .retain(|decl| !is_main_decl(decl));
        let qualified_fn_name = format!("{entry_module_path}.{}", test.function_name);
        let main_decl = build_test_main_decl(&qualified_fn_name, scenario_entry.module.span.file)?;
        scenario_entry.module.declarations.push(main_decl);

        let mut result = TestCaseResult {
            name: test.name,
            passed: true,
            iterations: test.iterations,
            diagnostics: Vec::new(),
            error: None,
        };

        let compiled_ctx = match typecheck_loaded_modules(&scenario_modules, &entry_module_path) {
            Ok(ctx) => ctx,
            Err(err) => {
                result.passed = false;
                result.error = Some(err);
                results.push(result);
                continue;
            }
        };
        result.diagnostics.extend(compiled_ctx.diagnostics.clone());

        for _ in 0..test.iterations {
            match execute_jit(&compiled_ctx) {
                Ok(run) => {
                    result.diagnostics.extend(run.diagnostics);
                    if run.exit_code != 0 {
                        result.passed = false;
                        result.error = Some(format!(
                            "test returned non-zero exit code {}",
                            run.exit_code
                        ));
                        break;
                    }
                }
                Err(err) => {
                    result.passed = false;
                    result.error = Some(err);
                    break;
                }
            }
        }

        results.push(result);
    }

    Ok(TestRunResult { cases: results })
}

fn run_on_compiler_stack<T, F>(label: &'static str, job: F) -> Result<T, String>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, String> + Send + 'static,
{
    let worker = std::thread::Builder::new()
        .name(format!("kea-{label}"))
        .stack_size(COMPILER_WORKER_STACK_BYTES)
        .spawn(job)
        .map_err(|err| format!("failed to spawn compiler worker thread for {label}: {err}"))?;

    match worker.join() {
        Ok(result) => result,
        Err(payload) => Err(format!(
            "compiler worker thread panicked during {label}: {}",
            panic_payload_message(payload)
        )),
    }
}

fn panic_payload_message(payload: Box<dyn Any + Send + 'static>) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_string()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "unknown panic payload".to_string()
    }
}

pub fn emit_diagnostics(diags: &[Diagnostic]) {
    for diag in diags {
        eprintln!("{diag}");
    }
}

pub fn process_module_in_env(
    module: &Module,
    env: &mut TypeEnv,
    records: &mut RecordRegistry,
    traits: &mut TraitRegistry,
    sum_types: &mut SumTypeRegistry,
    mut diagnostics: Vec<Diagnostic>,
) -> Result<ModuleProcessResult, Vec<Diagnostic>> {
    let module = prepare_module_for_compilation(module, &mut diagnostics);

    diagnostics.extend(validate_module_fn_annotations(&module));
    diagnostics.extend(validate_module_annotations(&module));
    let unsafe_registry = env.module_unsafe_function_registry();
    let unsafe_names = env.unsafe_function_names();
    diagnostics.extend(validate_unsafe_call_sites(
        &module,
        None,
        Some(&unsafe_registry),
        Some(&unsafe_names),
    ));
    warn_missing_module_doc(&module, &mut diagnostics);
    if has_errors(&diagnostics) {
        return Err(diagnostics);
    }

    let (module, block_method_owners) = lift_type_block_methods(&module);
    if register_top_level_declarations(
        &module,
        env,
        records,
        traits,
        sum_types,
        &mut diagnostics,
        None,
    )
    .is_err()
    {
        return Err(diagnostics);
    }

    let (expr_types, resolved_trait_callees) = match typecheck_functions(
        &module,
        env,
        records,
        traits,
        sum_types,
        &mut diagnostics,
        None,
        &block_method_owners,
    ) {
        Ok(et) => et,
        Err(_) => return Err(diagnostics),
    };

    let hir = lower_module(&module, env, &expr_types, &resolved_trait_callees);
    let hir = kea_hir::monomorphize::monomorphize(&hir);
    let explicit_borrow_param_map = collect_borrow_param_positions(&module, None);
    let borrow_param_map = infer_auto_borrow_param_positions(&hir, &explicit_borrow_param_map);
    diagnostics.extend(check_unique_moves_with_borrow_map(&hir, &borrow_param_map));
    if has_errors(&diagnostics) {
        return Err(diagnostics);
    }
    diagnostics.extend(validate_fip_annotations(&module, &hir));
    if has_errors(&diagnostics) {
        return Err(diagnostics);
    }

    let bindings = module
        .declarations
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Function(fn_decl) => Some((fn_decl.name.node.clone(), "fn".to_string())),
            DeclKind::ExprFn(expr_decl) => Some((expr_decl.name.node.clone(), "expr".to_string())),
            _ => None,
        })
        .map(|(name, kind)| {
            let ty = env
                .lookup(&name)
                .map(|scheme| sanitize_type_display(&scheme.ty))
                .unwrap_or_else(|| "?".to_string());
            ModuleBinding { name, kind, ty }
        })
        .collect();

    Ok(ModuleProcessResult {
        bindings,
        diagnostics,
    })
}

#[derive(Debug, Clone)]
struct LoadedModule {
    module_path: String,
    module: Module,
    origin: ModuleOrigin,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ModuleOrigin {
    Local,
    Stdlib,
    Dependency { package_name: String },
}

#[derive(Debug, Clone)]
struct DependencyRoot {
    package_name: String,
    src_root: PathBuf,
}

#[derive(Debug, Clone)]
struct ResolvedModulePath {
    file_path: PathBuf,
    origin: ModuleOrigin,
}

#[derive(Debug)]
struct ModuleResolver {
    stdlib_roots: Vec<PathBuf>,
    source_roots: Vec<PathBuf>,
    package_roots: BTreeMap<String, DependencyRoot>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DependencyResolutionProfile {
    Build,
    Test,
}

impl ModuleResolver {
    fn for_entry(entry: &Path, profile: DependencyResolutionProfile) -> Result<Self, String> {
        let mut stdlib_roots = Vec::new();
        if let Ok(path) = std::env::var("KEA_STDLIB_PATH") {
            stdlib_roots.push(PathBuf::from(path));
        }
        if let Ok(cwd) = std::env::current_dir() {
            stdlib_roots.push(cwd.join("stdlib"));
        }
        for ancestor in entry.ancestors() {
            stdlib_roots.push(ancestor.join("stdlib"));
        }
        if let Some(workspace_root) = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
        {
            stdlib_roots.push(workspace_root.join("stdlib"));
        }

        let mut source_roots = Vec::new();
        if let Some(src_root) = entry
            .ancestors()
            .find(|path| path.file_name().and_then(|name| name.to_str()) == Some("src"))
        {
            source_roots.push(src_root.to_path_buf());
        }
        if let Some(parent) = entry.parent() {
            source_roots.push(parent.to_path_buf());
        }
        if let Ok(cwd) = std::env::current_dir() {
            source_roots.push(cwd.join("src"));
            source_roots.push(cwd);
        }

        let stdlib_roots = dedup_existing_paths(stdlib_roots);
        let source_roots = dedup_existing_paths(source_roots);

        let mut package_roots = BTreeMap::new();
        let graph = match profile {
            DependencyResolutionProfile::Build => resolve_graph_for_entry(entry)?,
            DependencyResolutionProfile::Test => resolve_graph_for_test_entry(entry)?,
        };
        if let Some(graph) = graph {
            let dep_namespaces = dependency_namespaces(&graph);
            for namespace in dep_namespaces {
                if local_namespace_exists(&namespace, &source_roots) {
                    return Err(format!(
                        "dependency namespace collision: `{namespace}` exists as both a dependency and a local module; rename one to resolve ambiguity"
                    ));
                }
            }
            for (namespace, root) in graph.package_roots {
                package_roots.insert(
                    namespace,
                    DependencyRoot {
                        package_name: root.package_name,
                        src_root: root.src_root,
                    },
                );
            }
        }

        Ok(Self {
            stdlib_roots,
            source_roots,
            package_roots,
        })
    }

    fn resolve_with_origin(&self, module_path: &str) -> Option<ResolvedModulePath> {
        let segments = module_path
            .split('.')
            .filter(|segment| !segment.is_empty())
            .collect::<Vec<_>>();
        if segments.is_empty() {
            return None;
        }

        if let Some(dep_root) = self.package_roots.get(segments[0]) {
            let dep_rel = if segments.len() == 1 {
                vec![package_root_module_stem(&dep_root.package_name)]
            } else {
                segments[1..]
                    .iter()
                    .map(|segment| segment.to_ascii_lowercase())
                    .collect::<Vec<_>>()
            };
            let mut dep_rel_path = PathBuf::new();
            for part in dep_rel {
                dep_rel_path.push(part);
            }
            dep_rel_path.set_extension("kea");
            let candidate = dep_root.src_root.join(dep_rel_path);
            if candidate.is_file() {
                return Some(ResolvedModulePath {
                    file_path: candidate,
                    origin: ModuleOrigin::Dependency {
                        package_name: dep_root.package_name.clone(),
                    },
                });
            }
        }

        let rel_path = module_rel_path(segments.iter().copied());

        for root in &self.source_roots {
            let candidate = root.join(&rel_path);
            if candidate.is_file() {
                return Some(ResolvedModulePath {
                    file_path: candidate,
                    origin: ModuleOrigin::Local,
                });
            }
        }
        for root in &self.stdlib_roots {
            let candidate = root.join(&rel_path);
            if candidate.is_file() {
                return Some(ResolvedModulePath {
                    file_path: candidate,
                    origin: ModuleOrigin::Stdlib,
                });
            }
        }
        None
    }
}

fn dedup_existing_paths(paths: Vec<PathBuf>) -> Vec<PathBuf> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for path in paths {
        if !path.is_dir() {
            continue;
        }
        let canonical = fs::canonicalize(&path).unwrap_or(path);
        if seen.insert(canonical.clone()) {
            out.push(canonical);
        }
    }
    out
}

fn module_rel_path<'a>(segments: impl Iterator<Item = &'a str>) -> PathBuf {
    let mut rel_path = PathBuf::new();
    for segment in segments {
        rel_path.push(segment.to_ascii_lowercase());
    }
    rel_path.set_extension("kea");
    rel_path
}

fn package_root_module_stem(package_name: &str) -> String {
    package_name.replace('-', "_").to_ascii_lowercase()
}

fn local_namespace_exists(namespace: &str, source_roots: &[PathBuf]) -> bool {
    let stem = namespace.to_ascii_lowercase();
    source_roots.iter().any(|root| {
        root.join(format!("{stem}.kea")).is_file() || root.join(&stem).is_dir()
    })
}

fn parse_module_file(path: &Path, file_id: FileId) -> Result<Module, String> {
    let source = fs::read_to_string(path)
        .map_err(|err| format!("failed to read `{}`: {err}", path.display()))?;
    let (tokens, _) = lex_layout(&source, file_id)
        .map_err(|diags| format_diagnostics("lexing failed", &diags))?;
    parse_module(tokens, file_id).map_err(|diags| format_diagnostics("parsing failed", &diags))
}

fn pascal_case_segment(segment: &str) -> String {
    let mut out = String::new();
    for part in segment
        .split(|ch: char| !ch.is_ascii_alphanumeric())
        .filter(|part| !part.is_empty())
    {
        let mut chars = part.chars();
        if let Some(first) = chars.next() {
            out.push(first.to_ascii_uppercase());
            out.extend(chars);
        }
    }
    if out.is_empty() {
        "Main".to_string()
    } else {
        out
    }
}

fn module_path_from_entry(entry: &Path) -> String {
    let stem = entry
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("main");
    pascal_case_segment(stem)
}

fn module_struct_name(module_path: &str) -> &str {
    module_path.rsplit('.').next().unwrap_or(module_path)
}

fn module_has_same_name_type(module: &Module, struct_name: &str) -> bool {
    module.declarations.iter().any(|decl| match &decl.node {
        DeclKind::TypeDef(def) => def.name.node == struct_name,
        DeclKind::RecordDef(def) => def.name.node == struct_name,
        DeclKind::AliasDecl(alias) => alias.name.node == struct_name,
        DeclKind::OpaqueTypeDef(opaque) => opaque.name.node == struct_name,
        _ => false,
    })
}

fn configured_prelude_modules() -> Vec<String> {
    if let Ok(configured) = std::env::var("KEA_PRELUDE_MODULES") {
        return configured
            .split(',')
            .map(str::trim)
            .filter(|segment| !segment.is_empty())
            .map(ToOwned::to_owned)
            .collect();
    }
    vec!["Prelude".to_string(), "Show".to_string()]
}

fn configured_prelude_reexports() -> Vec<(String, String)> {
    let configured = std::env::var("KEA_PRELUDE_REEXPORTS").unwrap_or_else(|_| {
        "Order.Ordering,Option.Some,Option.None,Result.Ok,Result.Err,Show.show".to_string()
    });
    configured
        .split(',')
        .filter_map(|entry| {
            let trimmed = entry.trim();
            let (module, item) = trimmed.rsplit_once('.')?;
            if module.is_empty() || item.is_empty() {
                return None;
            }
            Some((module.to_string(), item.to_string()))
        })
        .collect()
}

fn apply_hardcoded_prelude_reexports(env: &mut TypeEnv, traits: &TraitRegistry) {
    for (module_path, item_name) in configured_prelude_reexports() {
        if let Some(scheme) = env.resolve_qualified(&module_path, &item_name).cloned() {
            env.bind(item_name.clone(), scheme);
            if let Some(signature) = env
                .resolve_qualified_function_signature(&module_path, &item_name)
                .cloned()
            {
                env.set_function_signature(item_name.clone(), signature);
            }
            if let Some(effect_row) = env.resolve_qualified_effect_row(&module_path, &item_name) {
                env.set_function_effect_row(item_name.clone(), effect_row);
            }
        }
        let owner_tag = format!("project:{module_path}");
        if traits.trait_owner(&item_name) == Some(owner_tag.as_str()) {
            env.mark_trait_in_scope(&item_name);
        }
    }
}

#[derive(Debug, Clone)]
struct RunnerTestCase {
    name: String,
    function_name: String,
    iterations: usize,
}

fn strip_test_decls_for_runner(module: &Module) -> (Module, Vec<RunnerTestCase>) {
    let mut declarations = Vec::new();
    let mut tests = Vec::new();
    let mut next_test_idx: usize = 0;

    for decl in &module.declarations {
        match &decl.node {
            DeclKind::Test(test_decl) => {
                let generated_name = format!("__kea_test_case_{next_test_idx}");
                next_test_idx += 1;
                declarations.push(test_decl_to_fn_decl(test_decl, &generated_name));
                tests.push(RunnerTestCase {
                    name: test_decl.name.node.clone(),
                    function_name: generated_name,
                    iterations: test_decl.iterations.unwrap_or(if test_decl.is_property {
                        100
                    } else {
                        1
                    }),
                });
            }
            _ => declarations.push(decl.clone()),
        }
    }

    (
        Module {
            doc: module.doc.clone(),
            annotations: module.annotations.clone(),
            declarations,
            span: module.span,
        },
        tests,
    )
}

fn test_decl_to_fn_decl(test_decl: &TestDecl, generated_name: &str) -> kea_ast::Decl {
    let fn_decl = FnDecl {
        public: false,
        name: kea_ast::Spanned::new(generated_name.to_string(), test_decl.name.span),
        doc: None,
        annotations: Vec::new(),
        params: Vec::new(),
        // Synthetic test functions: clear return_annotation so the purity
        // validator skips them.  Test bodies may use any effects (Fail,
        // IO, Net, etc.) depending on what they test.
        return_annotation: None,
        effect_annotation: None,
        body: test_decl.body.clone(),
        span: test_decl.span,
        where_clause: Vec::new(),
    };
    kea_ast::Spanned::new(DeclKind::Function(fn_decl), test_decl.span)
}

fn is_main_decl(decl: &kea_ast::Decl) -> bool {
    match &decl.node {
        DeclKind::Function(fn_decl) => fn_decl.name.node == "main",
        DeclKind::ExprFn(expr_decl) => expr_decl.name.node == "main",
        _ => false,
    }
}

fn prepare_module_for_compilation(module: &Module, diagnostics: &mut Vec<Diagnostic>) -> Module {
    let with_derived_impls = expand_derived_impls(module, diagnostics);
    expand_impl_methods_for_codegen(&with_derived_impls)
}

fn derive_trait_arg_name(arg: &Argument) -> Option<String> {
    if arg.label.is_some() {
        return None;
    }
    let candidate = match &arg.value.node {
        ExprKind::Var(name) => Some(name.clone()),
        ExprKind::Constructor { name, args } if args.is_empty() => Some(name.node.clone()),
        _ => None,
    }?;
    if candidate
        .chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_uppercase())
    {
        Some(candidate)
    } else {
        None
    }
}

fn derive_traits_from_annotations(
    annotations: &[Annotation],
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<String> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    for ann in annotations {
        if ann.name.node != "derive" {
            continue;
        }
        if ann.args.is_empty() {
            diagnostics.push(
                Diagnostic::error(
                    Category::TypeError,
                    "`@derive` requires at least one trait name argument",
                )
                .at(span_to_loc(ann.span)),
            );
            continue;
        }
        for arg in &ann.args {
            let Some(trait_name) = derive_trait_arg_name(arg) else {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "derive arguments must be positional UpperIdent trait names (e.g. `@derive(Eq, Show)`)",
                    )
                    .at(span_to_loc(arg.value.span)),
                );
                continue;
            };
            if seen.insert(trait_name.clone()) {
                out.push(trait_name);
            }
        }
    }
    out
}

fn type_annotation_mentions_param(ann: &TypeAnnotation, param: &str) -> bool {
    match ann {
        TypeAnnotation::Named(name) => name == param,
        TypeAnnotation::Applied(name, args) => {
            name == param
                || args
                    .iter()
                    .any(|arg| type_annotation_mentions_param(arg, param))
        }
        TypeAnnotation::Row { fields, .. } => fields
            .iter()
            .any(|(_, ty)| type_annotation_mentions_param(ty, param)),
        TypeAnnotation::EffectRow(effect_row) => effect_row.effects.iter().any(|item| {
            item.payload
                .as_ref()
                .is_some_and(|payload| type_annotation_mentions_param(payload, param))
        }),
        TypeAnnotation::Tuple(items) => items
            .iter()
            .any(|item| type_annotation_mentions_param(item, param)),
        TypeAnnotation::Forall { ty, .. } => type_annotation_mentions_param(ty, param),
        TypeAnnotation::Function(params, ret) => {
            params
                .iter()
                .any(|item| type_annotation_mentions_param(item, param))
                || type_annotation_mentions_param(ret, param)
        }
        TypeAnnotation::FunctionWithEffect(params, effect, ret) => {
            params
                .iter()
                .any(|item| type_annotation_mentions_param(item, param))
                || type_annotation_mentions_param(ret, param)
                || matches!(
                    &effect.node,
                    kea_ast::EffectAnnotation::Row(row)
                        if row.effects.iter().any(|item| {
                            item.payload.as_ref().is_some_and(|payload| {
                                type_annotation_mentions_param(payload, param)
                            })
                        })
                )
        }
        TypeAnnotation::Optional(inner) => type_annotation_mentions_param(inner, param),
        TypeAnnotation::Existential {
            associated_types, ..
        } => associated_types
            .iter()
            .any(|(_, ty)| type_annotation_mentions_param(ty, param)),
        TypeAnnotation::Projection { base, name } => base == param || name == param,
        TypeAnnotation::DimLiteral(_) => false,
    }
}

fn type_params_used_in_record(def: &RecordDef) -> Vec<String> {
    def.params
        .iter()
        .filter(|param| {
            def.fields
                .iter()
                .any(|(_, ty)| type_annotation_mentions_param(ty, param))
        })
        .cloned()
        .collect()
}

fn type_params_used_in_sum(def: &TypeDef) -> Vec<String> {
    def.params
        .iter()
        .filter(|param| {
            def.variants.iter().any(|variant| {
                variant
                    .fields
                    .iter()
                    .any(|field| type_annotation_mentions_param(&field.ty.node, param))
            })
        })
        .cloned()
        .collect()
}

fn impl_target_type(name: &str, params: &[String]) -> String {
    match params.len() {
        0 => name.to_string(),
        1 => format!("{name} {}", params[0]),
        // Two or more type params: use parenthesised form so that annotations
        // like `Result(a, e)` parse unambiguously.  Space-separated `Result a e`
        // would be misread as `Result(a(e))` by the recursive type-application
        // parser (the first type-var greedily consumes the second as its own arg).
        _ => format!("{name}({})", params.join(", ")),
    }
}

fn derive_where_clause(params: &[String], trait_name: &str) -> String {
    if params.is_empty() {
        String::new()
    } else {
        let bounds = params
            .iter()
            .map(|param| format!("{param}: {trait_name}"))
            .collect::<Vec<_>>()
            .join(", ");
        format!(" where {bounds}")
    }
}

fn constructor_pattern_fields(fields: &[VariantField], prefix: &str) -> (String, Vec<String>) {
    let mut vars = Vec::new();
    let mut parts = Vec::new();
    for (idx, field) in fields.iter().enumerate() {
        let var = format!("{prefix}{idx}");
        vars.push(var.clone());
        if let Some(name) = &field.name {
            parts.push(format!("{}: {var}", name.node));
        } else {
            parts.push(var);
        }
    }
    (parts.join(", "), vars)
}

fn eq_chain(left_vars: &[String], right_vars: &[String]) -> String {
    if left_vars.is_empty() {
        "true".to_string()
    } else {
        left_vars
            .iter()
            .zip(right_vars.iter())
            .map(|(left, right)| format!("({left} == {right})"))
            .collect::<Vec<_>>()
            .join(" and ")
    }
}

fn show_concat_for_constructor(variant_name: &str, vars: &[String]) -> String {
    if vars.is_empty() {
        return format!("\"{variant_name}\"");
    }
    let mut parts = vec![format!("\"{variant_name}(\"")];
    for (idx, var) in vars.iter().enumerate() {
        if idx > 0 {
            parts.push("\", \"".to_string());
        }
        parts.push(format!("Show.show({var})"));
    }
    parts.push("\")\"".to_string());
    parts.join(" ++ ")
}

fn show_concat_for_record(record_name: &str, field_names: &[String]) -> String {
    if field_names.is_empty() {
        return format!("\"{record_name}()\"");
    }
    let mut parts = vec![format!("\"{record_name}(\"")];
    for (idx, field) in field_names.iter().enumerate() {
        if idx > 0 {
            parts.push("\", \"".to_string());
        }
        parts.push(format!("\"{field}: \""));
        parts.push(format!("Show.show(x.{field})"));
    }
    parts.push("\")\"".to_string());
    parts.join(" ++ ")
}

fn ord_compare_chain_lines(comparisons: &[(String, String)], indent: usize) -> Vec<String> {
    if comparisons.is_empty() {
        return vec![format!("{}Order.Equal", " ".repeat(indent))];
    }
    let (left, right) = &comparisons[0];
    let pad = " ".repeat(indent);
    let mut lines = vec![
        format!("{pad}case Ord.compare({left}, {right})"),
        format!("{pad}  Order.Equal ->"),
    ];
    lines.extend(ord_compare_chain_lines(&comparisons[1..], indent + 4));
    lines.push(format!("{pad}  other -> other"));
    lines
}

fn hash_mix_expr(seed: impl Into<String>, fields: &[String]) -> String {
    fields.iter().fold(seed.into(), |acc, field| {
        format!("({acc} * 31 + Hash.hash({field}))")
    })
}

fn build_eq_impl_source_for_sum(def: &TypeDef) -> String {
    let used_params = type_params_used_in_sum(def);
    let target = impl_target_type(&def.name.node, &def.params);
    let where_clause = derive_where_clause(&used_params, "Eq");
    let mut source = String::new();
    source.push_str(&format!("{} as Eq{}\n", target, where_clause));
    source.push_str(&format!(
        "  fn eq(x: {}, y: {}) -> Bool\n",
        target, target
    ));
    source.push_str("    case x\n");
    for variant in &def.variants {
        let ctor = &variant.name.node;
        if variant.fields.is_empty() {
            source.push_str(&format!(
                "      {ctor} ->\n        case y\n          {ctor} -> true\n          _ -> false\n"
            ));
            continue;
        }
        let (left_pattern, left_vars) = constructor_pattern_fields(&variant.fields, "v");
        let (right_pattern, right_vars) = constructor_pattern_fields(&variant.fields, "w");
        let body = eq_chain(&left_vars, &right_vars);
        source.push_str(&format!(
            "      {ctor}({left_pattern}) ->\n        case y\n          {ctor}({right_pattern}) -> {body}\n          _ -> false\n"
        ));
    }
    source
}

fn build_eq_impl_source_for_record(def: &RecordDef) -> String {
    let used_params = type_params_used_in_record(def);
    let target = impl_target_type(&def.name.node, &def.params);
    let where_clause = derive_where_clause(&used_params, "Eq");
    let mut source = String::new();
    source.push_str(&format!("{} as Eq{}\n", target, where_clause));
    source.push_str(&format!(
        "  fn eq(a: {}, b: {}) -> Bool\n",
        target, target
    ));
    if def.fields.is_empty() {
        source.push_str("    true\n");
        return source;
    }
    let comparisons = def
        .fields
        .iter()
        .map(|(field, _)| format!("Eq.eq(a.{}, b.{})", field.node, field.node))
        .collect::<Vec<_>>()
        .join(" and ");
    source.push_str(&format!("    {comparisons}\n"));
    source
}

fn build_show_impl_source_for_sum(def: &TypeDef) -> String {
    let used_params = type_params_used_in_sum(def);
    let target = impl_target_type(&def.name.node, &def.params);
    let where_clause = derive_where_clause(&used_params, "Show");
    let mut source = String::new();
    source.push_str(&format!("{} as Show{}\n", target, where_clause));
    source.push_str(&format!("  fn show(x: {}) -> String\n", target));
    source.push_str("    case x\n");
    for variant in &def.variants {
        let ctor = &variant.name.node;
        if variant.fields.is_empty() {
            source.push_str(&format!("      {ctor} -> \"{ctor}\"\n"));
            continue;
        }
        let (pattern, vars) = constructor_pattern_fields(&variant.fields, "v");
        let body = show_concat_for_constructor(ctor, &vars);
        source.push_str(&format!("      {ctor}({pattern}) -> {body}\n"));
    }
    source
}

fn build_show_impl_source_for_record(def: &RecordDef) -> String {
    let used_params = type_params_used_in_record(def);
    let target = impl_target_type(&def.name.node, &def.params);
    let where_clause = derive_where_clause(&used_params, "Show");
    let mut source = String::new();
    source.push_str(&format!("{} as Show{}\n", target, where_clause));
    source.push_str(&format!("  fn show(x: {}) -> String\n", target));
    let field_names = def
        .fields
        .iter()
        .map(|(field, _)| field.node.clone())
        .collect::<Vec<_>>();
    source.push_str(&format!(
        "    {}\n",
        show_concat_for_record(&def.name.node, &field_names)
    ));
    source
}

fn build_ord_impl_source_for_sum(def: &TypeDef) -> String {
    let used_params = type_params_used_in_sum(def);
    let target = impl_target_type(&def.name.node, &def.params);
    let where_clause = derive_where_clause(&used_params, "Ord");
    let mut source = String::new();
    source.push_str(&format!("{} as Ord{}\n", target, where_clause));
    source.push_str(&format!(
        "  fn compare(x: {}, y: {}) -> Ordering\n",
        target, target
    ));
    source.push_str("    case x\n");
    for (variant_idx, variant) in def.variants.iter().enumerate() {
        let ctor = &variant.name.node;
        if variant.fields.is_empty() {
            source.push_str(&format!("      {ctor} ->\n"));
        } else {
            let (left_pattern, left_vars) = constructor_pattern_fields(&variant.fields, "v");
            source.push_str(&format!("      {ctor}({left_pattern}) ->\n"));
            source.push_str("        case y\n");
            for (other_idx, other) in def.variants.iter().enumerate() {
                let other_ctor = &other.name.node;
                if other_idx == variant_idx {
                    if other.fields.is_empty() {
                        source.push_str(&format!("          {other_ctor} -> Order.Equal\n"));
                    } else {
                        let (right_pattern, right_vars) =
                            constructor_pattern_fields(&other.fields, "w");
                        source.push_str(&format!("          {other_ctor}({right_pattern}) ->\n"));
                        let comparisons = left_vars
                            .iter()
                            .zip(right_vars.iter())
                            .map(|(left, right)| (left.clone(), right.clone()))
                            .collect::<Vec<_>>();
                        for line in ord_compare_chain_lines(&comparisons, 12) {
                            source.push_str(&line);
                            source.push('\n');
                        }
                    }
                } else {
                    let ordering = if variant_idx < other_idx {
                        "Order.Less"
                    } else {
                        "Order.Greater"
                    };
                    let wildcard_args = if other.fields.is_empty() {
                        String::new()
                    } else {
                        format!("({})", vec!["_"; other.fields.len()].join(", "))
                    };
                    source.push_str(&format!("          {other_ctor}{wildcard_args} -> {ordering}\n"));
                }
            }
            continue;
        }
        source.push_str("        case y\n");
        for (other_idx, other) in def.variants.iter().enumerate() {
            let other_ctor = &other.name.node;
            if other_idx == variant_idx {
                source.push_str(&format!("          {other_ctor} -> Order.Equal\n"));
            } else {
                let ordering = if variant_idx < other_idx {
                    "Order.Less"
                } else {
                    "Order.Greater"
                };
                let wildcard_args = if other.fields.is_empty() {
                    String::new()
                } else {
                    format!("({})", vec!["_"; other.fields.len()].join(", "))
                };
                source.push_str(&format!("          {other_ctor}{wildcard_args} -> {ordering}\n"));
            }
        }
    }
    source
}

fn build_ord_impl_source_for_record(def: &RecordDef) -> String {
    let used_params = type_params_used_in_record(def);
    let target = impl_target_type(&def.name.node, &def.params);
    let where_clause = derive_where_clause(&used_params, "Ord");
    let mut source = String::new();
    source.push_str(&format!("{} as Ord{}\n", target, where_clause));
    source.push_str(&format!(
        "  fn compare(a: {}, b: {}) -> Ordering\n",
        target, target
    ));
    if def.fields.is_empty() {
        source.push_str("    Order.Equal\n");
        return source;
    }
    let comparisons = def
        .fields
        .iter()
        .map(|(field, _)| (format!("a.{}", field.node), format!("b.{}", field.node)))
        .collect::<Vec<_>>();
    for line in ord_compare_chain_lines(&comparisons, 4) {
        source.push_str(&line);
        source.push('\n');
    }
    source
}

fn build_hash_impl_source_for_sum(def: &TypeDef) -> String {
    let used_params = type_params_used_in_sum(def);
    let target = impl_target_type(&def.name.node, &def.params);
    let where_clause = derive_where_clause(&used_params, "Hash");
    let mut source = String::new();
    source.push_str(&format!("{} as Hash{}\n", target, where_clause));
    source.push_str(&format!("  fn hash(x: {}) -> Int\n", target));
    source.push_str("    case x\n");
    for (variant_idx, variant) in def.variants.iter().enumerate() {
        let ctor = &variant.name.node;
        let seed = variant_idx.to_string();
        if variant.fields.is_empty() {
            source.push_str(&format!("      {ctor} -> {seed}\n"));
            continue;
        }
        let (pattern, vars) = constructor_pattern_fields(&variant.fields, "v");
        let expr = hash_mix_expr(seed, &vars);
        source.push_str(&format!("      {ctor}({pattern}) -> {expr}\n"));
    }
    source
}

fn build_hash_impl_source_for_record(def: &RecordDef) -> String {
    let used_params = type_params_used_in_record(def);
    let target = impl_target_type(&def.name.node, &def.params);
    let where_clause = derive_where_clause(&used_params, "Hash");
    let mut source = String::new();
    source.push_str(&format!("{} as Hash{}\n", target, where_clause));
    source.push_str(&format!("  fn hash(x: {}) -> Int\n", target));
    if def.fields.is_empty() {
        source.push_str("    0\n");
        return source;
    }
    let fields = def
        .fields
        .iter()
        .map(|(field, _)| format!("x.{}", field.node))
        .collect::<Vec<_>>();
    source.push_str(&format!("    {}\n", hash_mix_expr("0", &fields)));
    source
}

fn parse_generated_impl_decl(
    source: &str,
    file_id: FileId,
    context_span: Span,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<kea_ast::Decl> {
    let Ok((tokens, mut lex_diags)) = lex_layout(source, file_id) else {
        diagnostics.push(
            Diagnostic::error(
                Category::TypeError,
                "internal derive synthesis failed during lexing",
            )
            .at(span_to_loc(context_span)),
        );
        return None;
    };
    if !lex_diags.is_empty() {
        diagnostics.append(&mut lex_diags);
        return None;
    }
    let Ok(parsed) = parse_module(tokens, file_id) else {
        diagnostics.push(
            Diagnostic::error(
                Category::TypeError,
                "internal derive synthesis failed during parsing",
            )
            .at(span_to_loc(context_span)),
        );
        return None;
    };
    let Some(decl) = parsed.declarations.into_iter().next() else {
        diagnostics.push(
            Diagnostic::error(
                Category::TypeError,
                "internal derive synthesis produced no declarations",
            )
            .at(span_to_loc(context_span)),
        );
        return None;
    };
    if !matches!(decl.node, DeclKind::ImplBlock(_)) {
        diagnostics.push(
            Diagnostic::error(
                Category::TypeError,
                "internal derive synthesis did not produce an impl block",
            )
            .at(span_to_loc(context_span)),
        );
        return None;
    }
    Some(decl)
}

fn expand_derived_impls(module: &Module, diagnostics: &mut Vec<Diagnostic>) -> Module {
    let mut declarations = module.declarations.clone();
    let mut existing_impls: BTreeSet<(String, String)> = module
        .declarations
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::ImplBlock(ib) => Some((ib.trait_name.node.clone(), ib.type_name.node.clone())),
            _ => None,
        })
        .collect();

    for decl in &module.declarations {
        match &decl.node {
            DeclKind::TypeDef(def) => {
                let derive_traits = derive_traits_from_annotations(&def.annotations, diagnostics);
                for trait_name in derive_traits {
                    if existing_impls.contains(&(trait_name.clone(), def.name.node.clone())) {
                        continue;
                    }
                    let source = match trait_name.as_str() {
                        "Eq" => build_eq_impl_source_for_sum(def),
                        "Show" => build_show_impl_source_for_sum(def),
                        "Ord" => build_ord_impl_source_for_sum(def),
                        "Hash" => build_hash_impl_source_for_sum(def),
                        other => {
                            diagnostics.push(
                                Diagnostic::error(
                                    Category::TypeError,
                                    format!("unsupported derive trait `{other}`"),
                                )
                                .at(span_to_loc(decl.span)),
                            );
                            continue;
                        }
                    };
                    if let Some(impl_decl) =
                        parse_generated_impl_decl(&source, module.span.file, decl.span, diagnostics)
                    {
                        declarations.push(impl_decl);
                        existing_impls.insert((trait_name, def.name.node.clone()));
                    }
                }
            }
            DeclKind::RecordDef(def) => {
                let derive_traits = derive_traits_from_annotations(&def.annotations, diagnostics);
                for trait_name in derive_traits {
                    if existing_impls.contains(&(trait_name.clone(), def.name.node.clone())) {
                        continue;
                    }
                    let source = match trait_name.as_str() {
                        "Eq" => build_eq_impl_source_for_record(def),
                        "Show" => build_show_impl_source_for_record(def),
                        "Ord" => build_ord_impl_source_for_record(def),
                        "Hash" => build_hash_impl_source_for_record(def),
                        other => {
                            diagnostics.push(
                                Diagnostic::error(
                                    Category::TypeError,
                                    format!("unsupported derive trait `{other}`"),
                                )
                                .at(span_to_loc(decl.span)),
                            );
                            continue;
                        }
                    };
                    if let Some(impl_decl) =
                        parse_generated_impl_decl(&source, module.span.file, decl.span, diagnostics)
                    {
                        declarations.push(impl_decl);
                        existing_impls.insert((trait_name, def.name.node.clone()));
                    }
                }
            }
            _ => {}
        }
    }

    Module {
        doc: module.doc.clone(),
        annotations: module.annotations.clone(),
        declarations,
        span: module.span,
    }
}

fn build_test_main_decl(test_fn_name: &str, file_id: FileId) -> Result<kea_ast::Decl, String> {
    // Parse the body from source but strip return_annotation so the purity
    // validator skips the synthetic main (the guard checks
    // return_annotation.is_some()).  Test functions may use any effects.
    let source = format!("fn main() -> Int\n  {test_fn_name}()\n  0\n");
    let (tokens, _) = lex_layout(&source, file_id)
        .map_err(|diags| format_diagnostics("lexing failed", &diags))?;
    let module = parse_module(tokens, file_id)
        .map_err(|diags| format_diagnostics("parsing failed", &diags))?;
    let mut decl = module
        .declarations
        .into_iter()
        .next()
        .ok_or_else(|| "failed to build synthetic test main declaration".to_string())?;
    // Clear annotations so the purity validator treats this as a
    // synthetic node rather than a user-written fn declaration.
    // Test functions may use any effects.
    if let DeclKind::Function(ref mut fn_decl) = decl.node {
        fn_decl.return_annotation = None;
        fn_decl.effect_annotation = None;
    }
    Ok(decl)
}

fn collect_project_modules(entry: &Path) -> Result<Vec<LoadedModule>, String> {
    collect_project_modules_with_profile(entry, DependencyResolutionProfile::Build)
}

fn collect_project_modules_for_tests(entry: &Path) -> Result<Vec<LoadedModule>, String> {
    collect_project_modules_with_profile(entry, DependencyResolutionProfile::Test)
}

fn collect_project_modules_with_profile(
    entry: &Path,
    profile: DependencyResolutionProfile,
) -> Result<Vec<LoadedModule>, String> {
    struct VisitState {
        next_file_id: u32,
        visiting: Vec<String>,
        visited: HashSet<String>,
        loaded: HashMap<String, LoadedModule>,
        order: Vec<String>,
    }

    impl VisitState {
        fn visit(
            &mut self,
            module_path: &str,
            file_path: &Path,
            origin: ModuleOrigin,
            resolver: &ModuleResolver,
        ) -> Result<(), String> {
            if let Some(idx) = self.visiting.iter().position(|name| name == module_path) {
                let mut cycle = self.visiting[idx..].to_vec();
                cycle.push(module_path.to_string());
                return Err(format!(
                    "circular module import detected: {}",
                    cycle.join(" -> ")
                ));
            }
            if self.visited.contains(module_path) {
                return Ok(());
            }

            let file_path = fs::canonicalize(file_path).unwrap_or_else(|_| file_path.to_path_buf());
            let file_id = FileId(self.next_file_id);
            self.next_file_id += 1;
            let module = parse_module_file(&file_path, file_id)?;

            self.visiting.push(module_path.to_string());
            for decl in &module.declarations {
                let DeclKind::Import(import) = &decl.node else {
                    continue;
                };
                let dep_module = import.module.node.clone();
                let resolved = resolver.resolve_with_origin(&dep_module).ok_or_else(|| {
                    format!(
                        "module `{dep_module}` not found while resolving imports for `{module_path}`"
                    )
                })?;
                self.visit(
                    &dep_module,
                    &resolved.file_path,
                    resolved.origin,
                    resolver,
                )?;
            }
            self.visiting.pop();

            self.visited.insert(module_path.to_string());
            self.order.push(module_path.to_string());
            self.loaded.insert(
                module_path.to_string(),
                LoadedModule {
                    module_path: module_path.to_string(),
                    module,
                    origin,
                },
            );
            Ok(())
        }
    }

    let entry_path = fs::canonicalize(entry)
        .map_err(|err| format!("failed to read `{}`: {err}", entry.display()))?;
    let resolver = ModuleResolver::for_entry(&entry_path, profile)?;
    let entry_module_path = module_path_from_entry(&entry_path);
    let mut state = VisitState {
        next_file_id: 0,
        visiting: Vec::new(),
        visited: HashSet::new(),
        loaded: HashMap::new(),
        order: Vec::new(),
    };

    for prelude in configured_prelude_modules() {
        if let Some(resolved) = resolver.resolve_with_origin(&prelude) {
            state.visit(&prelude, &resolved.file_path, resolved.origin, &resolver)?;
        }
    }

    state.visit(
        &entry_module_path,
        &entry_path,
        ModuleOrigin::Local,
        &resolver,
    )?;

    Ok(state
        .order
        .into_iter()
        .filter_map(|module_path| state.loaded.get(&module_path).cloned())
        .collect())
}

fn merge_modules_for_codegen(modules: &[(String, Module)], entry_module_path: &str) -> Module {
    fn upsert_function_decl(
        name: String,
        decl: kea_ast::Decl,
        declarations: &mut Vec<kea_ast::Decl>,
        function_decl_indices: &mut BTreeMap<String, usize>,
    ) {
        if let Some(idx) = function_decl_indices.get(&name).copied() {
            declarations[idx] = decl;
            return;
        }
        function_decl_indices.insert(name, declarations.len());
        declarations.push(decl);
    }

    /// Insert a bare-name declaration only when no module has claimed that
    /// bare name yet.  Used for non-entry modules so that their bare `foo`
    /// doesn't stomp over a prelude/earlier `foo` that the type environment
    /// already has a definitive type for.  The qualified `M.foo` is always
    /// registered by the caller so it remains reachable.
    fn insert_bare_if_absent(
        name: String,
        decl: kea_ast::Decl,
        declarations: &mut Vec<kea_ast::Decl>,
        function_decl_indices: &mut BTreeMap<String, usize>,
    ) {
        if function_decl_indices.contains_key(&name) {
            return;
        }
        function_decl_indices.insert(name, declarations.len());
        declarations.push(decl);
    }

    let mut declarations = Vec::new();
    let mut function_decl_indices: BTreeMap<String, usize> = BTreeMap::new();

    for (module_path, module) in modules {
        let is_entry = module_path == entry_module_path;
        for decl in &module.declarations {
            match &decl.node {
                DeclKind::Function(fn_decl) => {
                    // Entry module: override any earlier bare-name binding so
                    // its own functions are in scope unqualified (e.g., the
                    // primary module's `is_empty` beats a library `is_empty`).
                    // Non-entry modules: insert bare name only if not already
                    // claimed.  Two different libraries defining a function
                    // with the same bare name (e.g., List.length and
                    // Vector.length) would otherwise compile the bare `length`
                    // declaration against the wrong type-environment binding,
                    // producing a broken empty function body.
                    //
                    // Exception: synthesized trait bare aliases (marked with
                    // @kea_trait_bare_alias by expand_impl_methods_for_codegen)
                    // are never allowed to override stdlib/prelude names, even
                    // in the entry module.  A user trait named `Foldable` with
                    // a method named `fold` would otherwise override the
                    // stdlib's `List.fold` recursive definition, corrupting it.
                    let is_trait_bare_alias = fn_decl
                        .annotations
                        .iter()
                        .any(|a| a.name.node == "kea_trait_bare_alias");
                    if is_entry && !is_trait_bare_alias {
                        upsert_function_decl(
                            fn_decl.name.node.clone(),
                            decl.clone(),
                            &mut declarations,
                            &mut function_decl_indices,
                        );
                    } else {
                        insert_bare_if_absent(
                            fn_decl.name.node.clone(),
                            decl.clone(),
                            &mut declarations,
                            &mut function_decl_indices,
                        );
                    }

                    if fn_decl.name.node.contains('.') {
                        continue;
                    }

                    // Trait bare aliases (synthesized by expand_impl_methods_for_codegen)
                    // must not be re-qualified as `EntryModule.method` because the
                    // resulting short name (e.g. `fold` from `TestModule.fold`) would
                    // contaminate the monomorphization routing table and prevent
                    // stdlib functions with the same name from resolving correctly.
                    // The real dispatch targets (`Trait.fold`, `Trait.Type.fold`) are
                    // already registered above.
                    if is_trait_bare_alias {
                        continue;
                    }

                    let mut lifted = fn_decl.clone();
                    lifted.name.node = format!("{module_path}.{}", fn_decl.name.node);
                    upsert_function_decl(
                        lifted.name.node.clone(),
                        kea_ast::Spanned::new(DeclKind::Function(lifted), decl.span),
                        &mut declarations,
                        &mut function_decl_indices,
                    );
                }
                DeclKind::ExprFn(expr_decl) => {
                    if is_entry {
                        upsert_function_decl(
                            expr_decl.name.node.clone(),
                            decl.clone(),
                            &mut declarations,
                            &mut function_decl_indices,
                        );
                    } else {
                        insert_bare_if_absent(
                            expr_decl.name.node.clone(),
                            decl.clone(),
                            &mut declarations,
                            &mut function_decl_indices,
                        );
                    }

                    if expr_decl.name.node.contains('.') {
                        continue;
                    }

                    let mut lifted = expr_decl.clone();
                    lifted.name.node = format!("{module_path}.{}", expr_decl.name.node);
                    upsert_function_decl(
                        lifted.name.node.clone(),
                        kea_ast::Spanned::new(DeclKind::ExprFn(lifted), decl.span),
                        &mut declarations,
                        &mut function_decl_indices,
                    );
                }
                _ => declarations.push(decl.clone()),
            }
        }
    }

    Module {
        doc: None,
        annotations: vec![],
        declarations,
        // Merged project modules may originate from different files.
        // Keep a synthetic span to avoid cross-file merge assertions.
        span: Span::synthetic(),
    }
}

fn parse_and_typecheck_project(entry: &Path) -> Result<CompilationContext, String> {
    let loaded_modules = collect_project_modules(entry)?;
    let entry_module_path = module_path_from_entry(entry);
    typecheck_loaded_modules(&loaded_modules, &entry_module_path)
}

fn typecheck_loaded_modules(
    loaded_modules: &[LoadedModule],
    entry_module_path: &str,
) -> Result<CompilationContext, String> {
    let prelude_modules: BTreeSet<String> = configured_prelude_modules().into_iter().collect();
    let mut env = TypeEnv::new();
    register_builtin_int_bitwise_methods(&mut env);
    register_builtin_ptr_ops(&mut env);
    let mut records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let mut sum_types = SumTypeRegistry::new();
    let mut diagnostics = Vec::new();
    let mut typed_modules = Vec::new();
    let mut all_expr_types = std::collections::BTreeMap::new();
    let mut all_resolved_trait_callees: std::collections::BTreeMap<Span, String> =
        std::collections::BTreeMap::new();
    let mut qualified_borrow_param_map = BTreeMap::new();
    let module_origins = loaded_modules
        .iter()
        .map(|loaded| (loaded.module_path.clone(), loaded.origin.clone()))
        .collect::<BTreeMap<_, _>>();
    for (module_path, origin) in &module_origins {
        env.register_module_package_scope(module_path, package_scope_for_origin(origin));
    }
    let unsafe_registry = collect_unsafe_function_registry(loaded_modules);
    for loaded in loaded_modules {
        let mut prepass_diags = Vec::new();
        let expanded = prepare_module_for_compilation(&loaded.module, &mut prepass_diags);
        for (name, positions) in
            collect_borrow_param_positions(&expanded, Some(&loaded.module_path))
        {
            if name.contains('.') {
                qualified_borrow_param_map.insert(name, positions);
            }
        }
    }

    for loaded in loaded_modules {
        env.set_current_package_scope(package_scope_for_origin(&loaded.origin));
        let is_entry_module = loaded.module_path == entry_module_path;
        let is_prelude_module = prelude_modules.contains(&loaded.module_path);
        let alias_snapshot = (!is_entry_module).then(|| env.snapshot_module_aliases());
        let trait_scope_snapshot = (!is_entry_module).then(|| env.snapshot_in_scope_traits());
        if !is_entry_module {
            env.push_scope();
        }

        let expanded = prepare_module_for_compilation(&loaded.module, &mut diagnostics);

        diagnostics.extend(validate_module_fn_annotations(&expanded));
        diagnostics.extend(validate_module_annotations(&expanded));
        diagnostics.extend(validate_unsafe_call_sites(
            &expanded,
            Some(&loaded.module_path),
            Some(&unsafe_registry),
            None,
        ));
        if has_errors(&diagnostics) {
            if !is_entry_module {
                env.pop_scope();
            }
            return Err(format_diagnostics(
                "type annotation validation failed",
                &diagnostics,
            ));
        }

        check_type_block_method_collisions(&expanded, Some(&loaded.module_path), &mut diagnostics);
        if has_errors(&diagnostics) {
            if !is_entry_module {
                env.pop_scope();
            }
            return Err(format_diagnostics("method collision", &diagnostics));
        }
        let (expanded, block_method_owners) = lift_type_block_methods(&expanded);

        register_top_level_declarations(
            &expanded,
            &mut env,
            &mut records,
            &mut traits,
            &mut sum_types,
            &mut diagnostics,
            Some(&loaded.module_path),
        )?;

        let imported_symbols = apply_module_imports(
            &expanded,
            &loaded.origin,
            &module_origins,
            &mut env,
            &traits,
            &mut diagnostics,
        )?;

        // String interpolation desugars to `show(...)` calls in the parser.
        // Re-export hardcoded prelude symbols before typechecking module bodies
        // so those calls resolve in user modules without explicit imports.
        apply_hardcoded_prelude_reexports(&mut env, &traits);

        // Bare trait method aliases (tagged @kea_trait_bare_alias) must not be
        // typechecked here: their bodies are identical to the qualified variant
        // (e.g. HasItem.fold) which is already typechecked. Letting them through
        // causes env["fold"] to be overwritten with the entry-module's monomorphic
        // type, corrupting type lookup for stdlib functions with the same name.
        let expanded_for_typeck = if is_entry_module {
            let mut filtered = expanded.clone();
            filtered.declarations.retain(|d| {
                let anns = match &d.node {
                    DeclKind::Function(f) => &f.annotations,
                    DeclKind::ExprFn(f) => &f.annotations,
                    _ => return true,
                };
                !has_annotation_named(anns, "kea_trait_bare_alias")
            });
            filtered
        } else {
            expanded.clone()
        };
        let (expr_types, resolved_trait_callees_chunk) = typecheck_functions(
            &expanded_for_typeck,
            &mut env,
            &mut records,
            &mut traits,
            &mut sum_types,
            &mut diagnostics,
            Some(&loaded.module_path),
            &block_method_owners,
        )?;

        all_expr_types.extend(expr_types);
        all_resolved_trait_callees.extend(resolved_trait_callees_chunk);
        let hir = lower_module(&expanded, &env, &all_expr_types, &all_resolved_trait_callees);
        let mut borrow_param_map = qualified_borrow_param_map.clone();
        borrow_param_map.extend(collect_borrow_param_positions(
            &expanded,
            Some(&loaded.module_path),
        ));
        borrow_param_map = infer_auto_borrow_param_positions(&hir, &borrow_param_map);
        diagnostics.extend(check_unique_moves_with_borrow_map(&hir, &borrow_param_map));
        if has_errors(&diagnostics) {
            if !is_entry_module {
                env.pop_scope();
            }
            return Err(format_diagnostics("move checking failed", &diagnostics));
        }
        for (name, positions) in &borrow_param_map {
            if name.contains('.') {
                qualified_borrow_param_map.insert(name.clone(), positions.clone());
            }
        }

        if !is_entry_module {
            let retained_qualified_bindings = declared_function_names(&expanded)
                .into_iter()
                .filter(|name| name.contains('.'))
                .filter_map(|name| env.lookup(&name).cloned().map(|scheme| (name, scheme)))
                .collect::<Vec<_>>();
            let retained_prelude_trait_bindings = if is_prelude_module {
                let module_owner = format!("project:{}", loaded.module_path);
                trait_method_names_for_owner(&module_owner, &traits)
                    .into_iter()
                    .filter_map(|name| env.lookup(&name).cloned().map(|scheme| (name, scheme)))
                    .collect::<Vec<_>>()
            } else {
                Vec::new()
            };
            for imported_name in imported_symbols {
                env.clear_function_metadata(&imported_name);
            }
            if !is_prelude_module && let Some(snapshot) = alias_snapshot {
                env.restore_module_aliases(snapshot);
            }
            if !is_prelude_module && let Some(snapshot) = trait_scope_snapshot {
                env.restore_in_scope_traits(snapshot);
            }
            env.pop_scope();
            for (name, scheme) in retained_qualified_bindings {
                env.bind(name, scheme);
            }
            for (name, scheme) in retained_prelude_trait_bindings {
                if env.lookup(&name).is_none() {
                    env.bind(name, scheme);
                }
            }
        }

        typed_modules.push((loaded.module_path.clone(), expanded));
    }

    apply_hardcoded_prelude_reexports(&mut env, &traits);
    env.set_current_package_scope(None);

    let module = merge_modules_for_codegen(&typed_modules, entry_module_path);
    let hir = lower_module(&module, &env, &all_expr_types, &all_resolved_trait_callees);
    let hir = kea_hir::monomorphize::monomorphize(&hir);
    diagnostics.extend(validate_fip_annotations(&module, &hir));
    if has_errors(&diagnostics) {
        return Err(format_diagnostics(
            "`@fip` verification failed",
            &diagnostics,
        ));
    }
    Ok(CompilationContext {
        module,
        hir,
        type_env: env,
        diagnostics,
    })
}

fn declared_function_names(module: &Module) -> Vec<String> {
    module
        .declarations
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Function(fn_decl) => Some(fn_decl.name.node.clone()),
            DeclKind::ExprFn(expr_decl) => Some(expr_decl.name.node.clone()),
            _ => None,
        })
        .collect()
}

fn trait_method_names_for_owner(owner: &str, traits: &TraitRegistry) -> BTreeSet<String> {
    let mut method_names = BTreeSet::new();
    for (trait_name, trait_owner) in traits.all_trait_owners() {
        if trait_owner != owner {
            continue;
        }
        if let Some(trait_info) = traits.lookup_trait(trait_name) {
            for method in &trait_info.methods {
                method_names.insert(method.name.clone());
            }
        }
    }
    method_names
}

fn bind_imported_item(
    module_path: &str,
    item_name: &str,
    span: Span,
    visibility: &ImportVisibility<'_>,
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    imported_symbols: &mut Vec<String>,
) {
    if env.module_item_inaccessible(module_path, item_name) {
        diagnostics.push(
            Diagnostic::error(
                Category::TypeError,
                format!("`{module_path}.{item_name}` is not public in its package"),
            )
            .at(SourceLocation {
                file_id: span.file.0,
                start: span.start,
                end: span.end,
            }),
        );
        return;
    }

    let Some(scheme) = env.resolve_qualified(module_path, item_name).cloned() else {
        let available = env
            .module_function_names(module_path)
            .unwrap_or_default()
            .join(", ");
        let mut diag = Diagnostic::error(
            Category::TypeError,
            format!("module `{module_path}` has no item `{item_name}`"),
        )
        .at(SourceLocation {
            file_id: span.file.0,
            start: span.start,
            end: span.end,
        });
        if !available.is_empty() {
            diag = diag.with_help(format!("available items: {available}"));
        }
        diagnostics.push(diag);
        return;
    };

    if let Some(target_origin) = visibility.module_origins.get(module_path)
        && crosses_package_boundary(visibility.current_origin, target_origin)
        && env.module_item_visibility(module_path, item_name) == Some(false)
    {
        diagnostics.push(
            Diagnostic::error(
                Category::TypeError,
                format!("`{module_path}.{item_name}` is not public in its package"),
            )
            .at(SourceLocation {
                file_id: span.file.0,
                start: span.start,
                end: span.end,
            }),
        );
        return;
    }

    env.bind(item_name.to_string(), prune_type_scheme_quantifiers(scheme));
    imported_symbols.push(item_name.to_string());

    if let Some(signature) = env
        .resolve_qualified_function_signature(module_path, item_name)
        .cloned()
    {
        env.set_function_signature(item_name.to_string(), signature);
    }
    if let Some(effect_row) = env.resolve_qualified_effect_row(module_path, item_name) {
        env.set_function_effect_row(item_name.to_string(), effect_row);
    }
}

fn prune_type_scheme_quantifiers(mut scheme: TypeScheme) -> TypeScheme {
    let free_tvs = free_type_vars(&scheme.ty);
    let free_rvs = free_row_vars(&scheme.ty);
    let free_dvs = free_dim_vars(&scheme.ty);

    scheme.type_vars.retain(|tv| free_tvs.contains(tv));
    scheme.row_vars.retain(|rv| free_rvs.contains(rv));
    scheme.dim_vars.retain(|dv| free_dvs.contains(dv));

    let quantified_type_vars = scheme.type_vars.iter().copied().collect::<BTreeSet<_>>();
    let quantified_row_vars = scheme.row_vars.iter().copied().collect::<BTreeSet<_>>();

    scheme
        .bounds
        .retain(|tv, _| quantified_type_vars.contains(tv));
    scheme
        .kinds
        .retain(|tv, _| quantified_type_vars.contains(tv));
    scheme
        .lacks
        .retain(|rv, _| quantified_row_vars.contains(rv));
    scheme
}

fn collect_import_aliases(module: &Module) -> BTreeMap<String, String> {
    let mut aliases = BTreeMap::new();
    for decl in &module.declarations {
        let DeclKind::Import(import) = &decl.node else {
            continue;
        };
        let module_path = import.module.node.clone();
        let alias = import
            .alias
            .as_ref()
            .map(|alias| alias.node.clone())
            .unwrap_or_else(|| {
                module_path
                    .rsplit('.')
                    .next()
                    .unwrap_or(module_path.as_str())
                    .to_string()
            });
        aliases.insert(alias, module_path);
    }
    aliases
}

fn extend_safe_forwarders_with_import_aliases(
    safe_handoff_callees: &mut BTreeMap<String, usize>,
    import_aliases: &BTreeMap<String, String>,
) {
    let originals = safe_handoff_callees
        .iter()
        .map(|(name, index)| (name.clone(), *index))
        .collect::<Vec<_>>();
    for (alias, module_path) in import_aliases {
        let prefix = format!("{module_path}.");
        for (original, index) in &originals {
            if let Some(rest) = original.strip_prefix(&prefix) {
                safe_handoff_callees.insert(format!("{alias}.{rest}"), *index);
            }
        }
    }
}

fn extend_safe_higher_order_forwarders_with_import_aliases(
    safe_higher_order_handoff_callees: &mut BTreeMap<String, SafeHigherOrderForwarder>,
    import_aliases: &BTreeMap<String, String>,
) {
    let originals = safe_higher_order_handoff_callees
        .iter()
        .map(|(name, spec)| (name.clone(), *spec))
        .collect::<Vec<_>>();
    for (alias, module_path) in import_aliases {
        let prefix = format!("{module_path}.");
        for (original, spec) in &originals {
            if let Some(rest) = original.strip_prefix(&prefix) {
                safe_higher_order_handoff_callees.insert(format!("{alias}.{rest}"), *spec);
            }
        }
    }
}

fn apply_module_imports(
    module: &Module,
    current_origin: &ModuleOrigin,
    module_origins: &BTreeMap<String, ModuleOrigin>,
    env: &mut TypeEnv,
    traits: &TraitRegistry,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<Vec<String>, String> {
    let visibility = ImportVisibility {
        current_origin,
        module_origins,
    };
    let mut imported_symbols = Vec::new();

    for decl in &module.declarations {
        let DeclKind::Import(import) = &decl.node else {
            continue;
        };

        let module_path = import.module.node.clone();
        let module_short = import
            .alias
            .as_ref()
            .map(|alias| alias.node.clone())
            .unwrap_or_else(|| {
                module_path
                    .rsplit('.')
                    .next()
                    .unwrap_or(module_path.as_str())
                    .to_string()
            });
        env.register_module_alias(&module_short, &module_path);
        let module_owner = format!("project:{module_path}");

        if matches!(import.items, ImportItems::Module) {
            for (trait_name, owner) in traits.all_trait_owners() {
                if owner == module_owner {
                    env.mark_trait_in_scope(trait_name);
                    if let Some(trait_info) = traits.lookup_trait(trait_name) {
                        for method in &trait_info.methods {
                            bind_imported_item(
                                &module_path,
                                &method.name,
                                import.module.span,
                                &visibility,
                                env,
                                diagnostics,
                                &mut imported_symbols,
                            );
                        }
                    }
                }
            }
            continue;
        }

        let ImportItems::Named(items) = &import.items else {
            continue;
        };

        for item in items {
            let item_name = item.node.clone();
            if traits.trait_owner(&item_name) == Some(module_owner.as_str()) {
                if let Some(target_origin) = visibility.module_origins.get(&module_path)
                    && crosses_package_boundary(visibility.current_origin, target_origin)
                    && env.module_item_visibility(&module_path, &item_name) == Some(false)
                {
                    diagnostics.push(
                        Diagnostic::error(
                            Category::TypeError,
                            format!("`{module_path}.{item_name}` is not public in its package"),
                        )
                        .at(SourceLocation {
                            file_id: item.span.file.0,
                            start: item.span.start,
                            end: item.span.end,
                        }),
                    );
                    continue;
                }
                env.mark_trait_in_scope(&item_name);
                imported_symbols.push(item_name);
                continue;
            }
            bind_imported_item(
                &module_path,
                &item_name,
                item.span,
                &visibility,
                env,
                diagnostics,
                &mut imported_symbols,
            );
        }
    }

    if has_errors(diagnostics) {
        return Err(format_diagnostics("import resolution failed", diagnostics));
    }

    Ok(imported_symbols)
}

struct ImportVisibility<'a> {
    current_origin: &'a ModuleOrigin,
    module_origins: &'a BTreeMap<String, ModuleOrigin>,
}

fn package_scope_for_origin(origin: &ModuleOrigin) -> Option<&str> {
    match origin {
        ModuleOrigin::Dependency { package_name } => Some(package_name.as_str()),
        ModuleOrigin::Local | ModuleOrigin::Stdlib => None,
    }
}

fn crosses_package_boundary(current: &ModuleOrigin, target: &ModuleOrigin) -> bool {
    match (current, target) {
        (
            ModuleOrigin::Dependency {
                package_name: current_package,
            },
            ModuleOrigin::Dependency {
                package_name: target_package,
            },
        ) => current_package != target_package,
        (ModuleOrigin::Dependency { .. }, ModuleOrigin::Local | ModuleOrigin::Stdlib) => false,
        (ModuleOrigin::Local | ModuleOrigin::Stdlib, ModuleOrigin::Dependency { .. }) => true,
        (ModuleOrigin::Local, ModuleOrigin::Local)
        | (ModuleOrigin::Stdlib, ModuleOrigin::Stdlib)
        | (ModuleOrigin::Local, ModuleOrigin::Stdlib)
        | (ModuleOrigin::Stdlib, ModuleOrigin::Local) => false,
    }
}

fn expand_impl_methods_for_codegen(module: &Module) -> Module {
    let mut declarations = module.declarations.clone();
    let mut trait_method_counts: BTreeMap<(String, String), usize> = BTreeMap::new();
    let mut bare_trait_method_counts: BTreeMap<String, usize> = BTreeMap::new();
    let locally_defined_traits: BTreeSet<String> = module
        .declarations
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::TraitDef(trait_def) => Some(trait_def.name.node.clone()),
            _ => None,
        })
        .collect();
    let mut existing_function_names: BTreeSet<String> = module
        .declarations
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Function(fn_decl) => Some(fn_decl.name.node.clone()),
            DeclKind::ExprFn(expr_decl) => Some(expr_decl.name.node.clone()),
            _ => None,
        })
        .collect();
    for decl in &module.declarations {
        let DeclKind::ImplBlock(impl_block) = &decl.node else {
            continue;
        };
        for method in &impl_block.methods {
            *trait_method_counts
                .entry((impl_block.trait_name.node.clone(), method.name.node.clone()))
                .or_insert(0) += 1;
            *bare_trait_method_counts
                .entry(method.name.node.clone())
                .or_insert(0) += 1;
        }
    }

    for decl in &module.declarations {
        let DeclKind::ImplBlock(impl_block) = &decl.node else {
            continue;
        };
        for method in &impl_block.methods {
            let mut lifted = method.clone();
            let trait_name = impl_block.trait_name.node.clone();
            let type_name = impl_block.type_name.node.clone();
            let method_name = method.name.node.clone();
            let duplicate_count = trait_method_counts
                .get(&(trait_name.clone(), method_name.clone()))
                .copied()
                .unwrap_or(1);
            // Always emit a disambiguated trait-method symbol.
            let typed_runtime_name = format!("{trait_name}.{type_name}.{method_name}");
            lifted.name.node = typed_runtime_name;
            declarations.push(kea_ast::Spanned::new(
                DeclKind::Function(lifted),
                method.span,
            ));

            // Keep `Trait.method` as a compatibility alias only when this
            // module defines the trait locally and contributes a single
            // implementation for the trait method.
            //
            // Without the local-trait guard, non-owner modules can leak
            // `Trait.method` aliases that collide with the owning module's
            // namespace and route calls to the wrong impl body.
            if duplicate_count == 1 && locally_defined_traits.contains(&trait_name) {
                let mut trait_alias = method.clone();
                trait_alias.name.node = format!("{trait_name}.{method_name}");
                declarations.push(kea_ast::Spanned::new(
                    DeclKind::Function(trait_alias),
                    method.span,
                ));
            }

            // Provide an unqualified alias only when the method name is unique
            // in this module and does not collide with an existing top-level
            // function. This keeps `x.method()` available for in-scope traits
            // while preserving deterministic dispatch.
            if bare_trait_method_counts
                .get(&method_name)
                .copied()
                .unwrap_or_default()
                == 1
                && existing_function_names.insert(method_name.clone())
            {
                let mut bare = method.clone();
                bare.name.node = method_name.clone();
                // Mark as a synthesized trait alias so merge_modules_for_codegen
                // treats it as non-overriding (insert_bare_if_absent).  This
                // prevents bare method names like `fold` from overriding stdlib
                // functions of the same name and corrupting their recursive calls.
                bare.annotations.push(kea_ast::Annotation {
                    name: kea_ast::Spanned::new(
                        "kea_trait_bare_alias".to_string(),
                        method.span,
                    ),
                    args: vec![],
                    span: method.span,
                });
                declarations.push(kea_ast::Spanned::new(DeclKind::Function(bare), method.span));
            }
        }
    }

    Module {
        doc: module.doc.clone(),
        annotations: module.annotations.clone(),
        declarations,
        span: module.span,
    }
}

/// Lift type-block methods (fn declarations inside struct/enum bodies) to
/// top-level `DeclKind::Function` entries so that the rest of the pipeline
/// (registration, type-checking, HIR lowering, MIR, codegen) sees them as
/// ordinary callable functions.
///
/// Returns the augmented module plus a map from method name → owner type name
/// so that `typecheck_functions` can register each method as inherent on its
/// nominal type rather than on the implicit module struct.
fn lift_type_block_methods(module: &Module) -> (Module, BTreeMap<String, String>) {
    let mut extra_decls: Vec<kea_ast::Decl> = Vec::new();
    let mut block_method_owners: BTreeMap<String, String> = BTreeMap::new();

    for decl in &module.declarations {
        let (type_name, methods): (&str, &[FnDecl]) = match &decl.node {
            DeclKind::RecordDef(r) => (&r.name.node, &r.methods),
            DeclKind::TypeDef(t) => (&t.name.node, &t.methods),
            _ => continue,
        };
        for method in methods {
            // Qualified-name lift only: enables static calls (`TypeName.method()` → `Var("TypeName.method")` in HIR).
            // The bare name (`"method"`) is registered in the type env for type inference of UMS calls
            // (`p.method()` → `Var("method")` → rewritten to `Var("TypeName.method")` via type_block_aliases).
            // We do NOT add a bare DeclKind::Function to avoid namespace collisions with stdlib functions.
            let mut qualified_method = method.clone();
            qualified_method.name = kea_ast::Spanned::new(
                format!("{type_name}.{}", method.name.node),
                method.name.span,
            );
            extra_decls.push(Spanned::new(
                DeclKind::Function(qualified_method),
                method.span,
            ));
            // Map qualified_name → owner_type_name so typecheck_functions registers it correctly.
            // Last writer wins for name → type; collision detection happens separately.
            block_method_owners.insert(
                format!("{type_name}.{}", method.name.node),
                type_name.to_string(),
            );
        }
    }

    if extra_decls.is_empty() {
        return (module.clone(), block_method_owners);
    }

    let mut declarations = module.declarations.clone();
    declarations.extend(extra_decls);
    let lifted = Module {
        doc: module.doc.clone(),
        annotations: module.annotations.clone(),
        declarations,
        span: module.span,
    };
    (lifted, block_method_owners)
}

/// Check for name collisions among type-block methods:
/// 1. Duplicate method names within a single type block.
/// 2. A type-block method name that collides with a file-scope function in a
///    same-name merged namespace (§11.6).
///
/// Returns a list of diagnostics; if any are errors the caller should abort.
fn check_type_block_method_collisions(
    module: &Module,
    module_path: Option<&str>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Some(module_path) = module_path else {
        return;
    };
    let struct_name = module_struct_name(module_path);

    let file_scope_fns: BTreeMap<String, Span> = module
        .declarations
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::Function(f) => Some((f.name.node.clone(), f.span)),
            DeclKind::ExprFn(e) => Some((e.name.node.clone(), e.span)),
            _ => None,
        })
        .collect();

    for decl in &module.declarations {
        let (type_name, methods): (&str, &[FnDecl]) = match &decl.node {
            DeclKind::RecordDef(r) => (&r.name.node, &r.methods),
            DeclKind::TypeDef(t) => (&t.name.node, &t.methods),
            _ => continue,
        };
        let is_merged = type_name == struct_name;
        let mut seen_in_block: BTreeMap<String, Span> = BTreeMap::new();

        for m in methods {
            if let Some(&prev_span) = seen_in_block.get(&m.name.node) {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!(
                            "duplicate method `{}` in `{}` block",
                            m.name.node, type_name
                        ),
                    )
                    .at(span_to_loc(m.span))
                    .with_label(span_to_loc(prev_span), "first definition here"),
                );
                return;
            }
            seen_in_block.insert(m.name.node.clone(), m.span);

            if is_merged
                && let Some(&fs_span) = file_scope_fns.get(&m.name.node) {
                    diagnostics.push(
                        Diagnostic::error(
                            Category::TypeError,
                            format!(
                                "method `{}` declared in `{}` block conflicts with a \
                                 file-scope function of the same name in the merged namespace",
                                m.name.node, type_name
                            ),
                        )
                        .at(span_to_loc(m.span))
                        .with_label(span_to_loc(fs_span), "file-scope definition here")
                        .with_help("rename one of the definitions, or remove the duplicate"),
                    );
                    return;
                }
        }
    }
}

fn register_top_level_declarations(
    module: &Module,
    env: &mut TypeEnv,
    records: &mut RecordRegistry,
    traits: &mut TraitRegistry,
    sum_types: &mut SumTypeRegistry,
    diagnostics: &mut Vec<Diagnostic>,
    module_path: Option<&str>,
) -> Result<(), String> {
    let owner = module_path
        .map(|path| format!("project:{path}"))
        .unwrap_or_else(|| "repl:".to_string());

    if let Some(module_path) = module_path {
        let struct_name = module_struct_name(module_path);
        env.register_module_alias(struct_name, module_path);
        env.register_module_struct(
            module_path,
            struct_name,
            module_has_same_name_type(module, struct_name),
        );
        for decl in &module.declarations {
            match &decl.node {
                DeclKind::Function(fn_decl) => {
                    env.register_module_item_visibility(
                        module_path,
                        &fn_decl.name.node,
                        fn_decl.public,
                    );
                }
                DeclKind::ExprFn(expr_decl) => {
                    env.register_module_item_visibility(
                        module_path,
                        &expr_decl.name.node,
                        expr_decl.public,
                    );
                }
                DeclKind::TypeDef(def) => {
                    env.register_module_item_visibility(module_path, &def.name.node, def.public);
                }
                DeclKind::AliasDecl(alias) => {
                    env.register_module_item_visibility(
                        module_path,
                        &alias.name.node,
                        alias.public,
                    );
                }
                DeclKind::OpaqueTypeDef(opaque) => {
                    env.register_module_item_visibility(
                        module_path,
                        &opaque.name.node,
                        opaque.public,
                    );
                }
                DeclKind::RecordDef(record) => {
                    env.register_module_item_visibility(
                        module_path,
                        &record.name.node,
                        record.public,
                    );
                }
                DeclKind::TraitDef(trait_def) => {
                    env.register_module_item_visibility(
                        module_path,
                        &trait_def.name.node,
                        trait_def.public,
                    );
                }
                DeclKind::EffectDecl(effect_decl) => {
                    env.register_module_item_visibility(
                        module_path,
                        &effect_decl.name.node,
                        effect_decl.public,
                    );
                }
                _ => {}
            }
        }
    }

    // Register nominal type ownership before impl registration so derived/manual
    // impls for module-defined enums/records/aliases/opaques satisfy orphan checks.
    for decl in &module.declarations {
        match &decl.node {
            DeclKind::TypeDef(def) => traits.register_type_owner(&def.name.node, &owner),
            DeclKind::RecordDef(def) => traits.register_type_owner(&def.name.node, &owner),
            DeclKind::AliasDecl(def) => traits.register_type_owner(&def.name.node, &owner),
            DeclKind::OpaqueTypeDef(def) => traits.register_type_owner(&def.name.node, &owner),
            _ => {}
        }
    }

    let record_defs: Vec<&RecordDef> = module
        .declarations
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::RecordDef(def) => Some(def),
            _ => None,
        })
        .collect();

    // Pass 1: register non-sum type declarations.
    // Alias/opaque definitions are recorded as annotations, and record names are
    // seeded before field validation to support mutual recursion with enums.
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
            _ => {}
        }
    }

    if let Err(diag) = records.register_names(&record_defs) {
        diagnostics.push(diag);
        return Err(format_diagnostics(
            "record registration failed",
            diagnostics,
        ));
    }

    let type_defs: Vec<&TypeDef> = module
        .declarations
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::TypeDef(def) => Some(def),
            _ => None,
        })
        .collect();

    if let Err(diag) = sum_types.register_names(&type_defs) {
        diagnostics.push(diag);
        return Err(format_diagnostics(
            "sum type registration failed",
            diagnostics,
        ));
    }

    if let Err(diag) = records.resolve_registered_fields(&record_defs, Some(sum_types)) {
        diagnostics.push(diag);
        return Err(format_diagnostics(
            "record registration failed",
            diagnostics,
        ));
    }

    if let Err(diag) = sum_types.resolve_registered_variants(&type_defs, records) {
        diagnostics.push(diag);
        return Err(format_diagnostics(
            "sum type registration failed",
            diagnostics,
        ));
    }

    // Validate alias targets now that all types are registered.
    if let Err(diag) = records.validate_alias_targets(Some(sum_types)) {
        diagnostics.push(diag);
        return Err(format_diagnostics(
            "alias target validation failed",
            diagnostics,
        ));
    }

    // Pass 2: register declarations that depend on types.
    for decl in &module.declarations {
        match &decl.node {
            DeclKind::TraitDef(trait_def) => {
                if let Err(diag) = traits.register_trait_with_owner_and_sum_types(
                    trait_def,
                    records,
                    Some(sum_types),
                    &owner,
                ) {
                    diagnostics.push(diag);
                    return Err(format_diagnostics("trait registration failed", diagnostics));
                }
                env.mark_trait_in_scope(&trait_def.name.node);
            }
            DeclKind::ImplBlock(impl_block) => {
                if let Err(diag) = traits.register_trait_impl_in_module(impl_block, &owner) {
                    diagnostics.push(diag);
                    return Err(format_diagnostics("impl registration failed", diagnostics));
                }
                let method_types = concrete_method_types_from_decls(
                    &impl_block.type_name.node,
                    &impl_block.methods,
                    records,
                    Some(sum_types),
                );
                if let Err(diag) = traits.add_impl_methods(method_types) {
                    traits.rollback_last_impl();
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

                // When an effect is declared inside a source module, expose its
                // operations through that module path as well (e.g. `use IO`
                // enables `IO.stdout(...)` from `stdlib/io.kea`) in addition to
                // the canonical effect namespace (`Kea.IO`).
                if let Some(module_path) = module_path {
                    let effect_module = effect_decl.name.node.clone();
                    for operation in &effect_decl.operations {
                        let op_name = operation.name.node.clone();
                        if let Some(scheme) =
                            env.resolve_qualified(&effect_module, &op_name).cloned()
                        {
                            env.register_module_function(module_path, &op_name);
                            env.register_module_type_scheme_exact(module_path, &op_name, scheme);

                            let qualified_name = format!("{module_path}.{op_name}");
                            if let Some(signature) = env
                                .resolve_qualified_function_signature(&effect_module, &op_name)
                                .cloned()
                            {
                                env.set_function_signature(qualified_name.clone(), signature);
                            }
                            if let Some(effect_row) =
                                env.resolve_qualified_effect_row(&effect_module, &op_name)
                            {
                                env.set_function_effect_row(qualified_name, effect_row);
                            }
                        }
                    }
                }
            }
            DeclKind::Import(_) => {}
            _ => {}
        }
    }

    register_record_const_fields(
        module,
        env,
        records,
        traits,
        sum_types,
        diagnostics,
        module_path,
    )?;

    Ok(())
}

fn const_expr_references(
    expr: &Expr,
    owner: &str,
    known: &BTreeSet<String>,
    refs: &mut BTreeSet<String>,
) {
    match &expr.node {
        ExprKind::Var(name) => {
            if known.contains(name) {
                refs.insert(name.clone());
            }
        }
        ExprKind::FieldAccess { expr, field } => {
            if let ExprKind::Var(qualifier) = &expr.node
                && qualifier == owner
                && known.contains(&field.node)
            {
                refs.insert(field.node.clone());
            }
            const_expr_references(expr, owner, known, refs);
        }
        ExprKind::Lit(_) | ExprKind::None | ExprKind::Atom(_) => {}
        ExprKind::UnaryOp { operand, .. } => const_expr_references(operand, owner, known, refs),
        ExprKind::Unsafe { body } => const_expr_references(body, owner, known, refs),
        ExprKind::BinaryOp { left, right, .. } => {
            const_expr_references(left, owner, known, refs);
            const_expr_references(right, owner, known, refs);
        }
        ExprKind::Tuple(items) | ExprKind::List(items) | ExprKind::Block(items) => {
            for item in items {
                const_expr_references(item, owner, known, refs);
            }
        }
        ExprKind::Record { fields, spread, .. } | ExprKind::AnonRecord { fields, spread } => {
            for (_, value) in fields {
                const_expr_references(value, owner, known, refs);
            }
            if let Some(base) = spread {
                const_expr_references(base, owner, known, refs);
            }
        }
        ExprKind::Update { base, fields } => {
            const_expr_references(base, owner, known, refs);
            for (_, value) in fields {
                const_expr_references(value, owner, known, refs);
            }
        }
        ExprKind::Constructor { args, .. } => {
            for arg in args {
                const_expr_references(&arg.value, owner, known, refs);
            }
        }
        ExprKind::StringInterp(parts) => {
            for part in parts {
                if let kea_ast::StringInterpPart::Expr(value) = part {
                    const_expr_references(value, owner, known, refs);
                }
            }
        }
        ExprKind::Range { start, end, .. } => {
            const_expr_references(start, owner, known, refs);
            const_expr_references(end, owner, known, refs);
        }
        ExprKind::As { expr, .. } => const_expr_references(expr, owner, known, refs),
        ExprKind::MapLiteral(entries) => {
            for (key, value) in entries {
                const_expr_references(key, owner, known, refs);
                const_expr_references(value, owner, known, refs);
            }
        }
        ExprKind::Call { .. }
        | ExprKind::Lambda { .. }
        | ExprKind::Let { .. }
        | ExprKind::If { .. }
        | ExprKind::Case { .. }
        | ExprKind::Cond { .. }
        | ExprKind::For(_)
        | ExprKind::With { .. }
        | ExprKind::Handle { .. }
        | ExprKind::Resume { .. }
        | ExprKind::WhenGuard { .. }
        | ExprKind::Yield { .. }
        | ExprKind::ActorSend { .. }
        | ExprKind::ActorCall { .. }
        | ExprKind::ControlSend { .. }
        | ExprKind::Wildcard => {}
    }
}

fn const_expr_supported(expr: &Expr) -> bool {
    match &expr.node {
        ExprKind::Lit(_) | ExprKind::None | ExprKind::Atom(_) | ExprKind::Var(_) => true,
        ExprKind::UnaryOp { operand, .. } => const_expr_supported(operand),
        ExprKind::Unsafe { .. } => false,
        ExprKind::BinaryOp { left, right, .. } => {
            const_expr_supported(left) && const_expr_supported(right)
        }
        ExprKind::Tuple(items) | ExprKind::List(items) | ExprKind::Block(items) => {
            items.iter().all(const_expr_supported)
        }
        ExprKind::Record { fields, spread, .. } | ExprKind::AnonRecord { fields, spread } => {
            fields.iter().all(|(_, value)| const_expr_supported(value))
                && spread
                    .as_ref()
                    .is_none_or(|base| const_expr_supported(base))
        }
        ExprKind::Update { base, fields } => {
            const_expr_supported(base)
                && fields.iter().all(|(_, value)| const_expr_supported(value))
        }
        ExprKind::Constructor { args, .. } => {
            args.iter().all(|arg| const_expr_supported(&arg.value))
        }
        ExprKind::StringInterp(parts) => parts.iter().all(|part| match part {
            kea_ast::StringInterpPart::Literal(_) => true,
            kea_ast::StringInterpPart::Expr(value) => const_expr_supported(value),
        }),
        ExprKind::Range { start, end, .. } => {
            const_expr_supported(start) && const_expr_supported(end)
        }
        ExprKind::As { expr, .. } => const_expr_supported(expr),
        ExprKind::MapLiteral(entries) => entries
            .iter()
            .all(|(key, value)| const_expr_supported(key) && const_expr_supported(value)),
        ExprKind::FieldAccess { expr, .. } => const_expr_supported(expr),
        ExprKind::Call { .. }
        | ExprKind::Lambda { .. }
        | ExprKind::Let { .. }
        | ExprKind::If { .. }
        | ExprKind::Case { .. }
        | ExprKind::Cond { .. }
        | ExprKind::For(_)
        | ExprKind::With { .. }
        | ExprKind::Handle { .. }
        | ExprKind::Resume { .. }
        | ExprKind::WhenGuard { .. }
        | ExprKind::Yield { .. }
        | ExprKind::ActorSend { .. }
        | ExprKind::ActorCall { .. }
        | ExprKind::ControlSend { .. }
        | ExprKind::Wildcard => false,
    }
}

fn topo_sort_const_fields(def: &RecordDef) -> Result<Vec<String>, BTreeSet<String>> {
    let mut deps: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let known = def
        .const_fields
        .iter()
        .map(|field| field.name.node.clone())
        .collect::<BTreeSet<_>>();
    for field in &def.const_fields {
        let mut refs = BTreeSet::new();
        const_expr_references(&field.value, &def.name.node, &known, &mut refs);
        deps.insert(field.name.node.clone(), refs);
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mark {
        Temp,
        Perm,
    }

    fn visit(
        name: &str,
        deps: &BTreeMap<String, BTreeSet<String>>,
        marks: &mut BTreeMap<String, Mark>,
        stack: &mut Vec<String>,
        order: &mut Vec<String>,
    ) -> Result<(), BTreeSet<String>> {
        if matches!(marks.get(name), Some(Mark::Perm)) {
            return Ok(());
        }
        if matches!(marks.get(name), Some(Mark::Temp)) {
            let start = stack.iter().position(|item| item == name).unwrap_or(0);
            return Err(stack[start..].iter().cloned().collect());
        }

        marks.insert(name.to_string(), Mark::Temp);
        stack.push(name.to_string());
        if let Some(children) = deps.get(name) {
            for child in children {
                visit(child, deps, marks, stack, order)?;
            }
        }
        stack.pop();
        marks.insert(name.to_string(), Mark::Perm);
        order.push(name.to_string());
        Ok(())
    }

    let mut marks = BTreeMap::new();
    let mut order = Vec::new();
    let mut stack = Vec::new();
    for field in &def.const_fields {
        visit(&field.name.node, &deps, &mut marks, &mut stack, &mut order)?;
    }
    Ok(order)
}

fn register_record_const_fields(
    module: &Module,
    env: &mut TypeEnv,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
    diagnostics: &mut Vec<Diagnostic>,
    module_path: Option<&str>,
) -> Result<(), String> {
    for decl in &module.declarations {
        let DeclKind::RecordDef(def) = &decl.node else {
            continue;
        };
        if def.const_fields.is_empty() {
            continue;
        }

        let mut const_types = BTreeMap::<String, Type>::new();
        for const_field in &def.const_fields {
            let Some(resolved) =
                resolve_annotation(&const_field.annotation, records, Some(sum_types))
            else {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!(
                            "unknown type annotation in const field `{}.{}`",
                            def.name.node, const_field.name.node
                        ),
                    )
                    .at(SourceLocation {
                        file_id: const_field.name.span.file.0,
                        start: const_field.name.span.start,
                        end: const_field.name.span.end,
                    }),
                );
                return Err(format_diagnostics(
                    "const field registration failed",
                    diagnostics,
                ));
            };
            const_types.insert(const_field.name.node.clone(), resolved);
        }

        let order = match topo_sort_const_fields(def) {
            Ok(order) => order,
            Err(cycle) => {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!(
                            "circular const dependency in `{}`: {}",
                            def.name.node,
                            cycle.into_iter().collect::<Vec<_>>().join(" -> ")
                        ),
                    )
                    .at(SourceLocation {
                        file_id: def.name.span.file.0,
                        start: def.name.span.start,
                        end: def.name.span.end,
                    }),
                );
                return Err(format_diagnostics(
                    "const field registration failed",
                    diagnostics,
                ));
            }
        };

        for (const_name, const_ty) in &const_types {
            let scheme = TypeScheme::mono(const_ty.clone());
            env.bind(format!("{}.{}", def.name.node, const_name), scheme.clone());
            if env.resolve_module_path_alias(&def.name.node).is_none() {
                env.register_module_alias(&def.name.node, &def.name.node);
            }
            env.register_module_type_scheme_exact(&def.name.node, const_name, scheme.clone());
            env.register_module_item_visibility(&def.name.node, const_name, def.public);
            if let Some(module_path) = module_path
                && module_struct_name(module_path) == def.name.node
            {
                env.register_module_type_scheme_exact(module_path, const_name, scheme.clone());
                env.register_module_item_visibility(module_path, const_name, def.public);
            }
        }

        env.push_scope();
        for (const_name, const_ty) in &const_types {
            env.bind(const_name.clone(), TypeScheme::mono(const_ty.clone()));
        }

        for const_name in order {
            let Some(const_field) = def
                .const_fields
                .iter()
                .find(|field| field.name.node == const_name)
            else {
                continue;
            };
            if !const_expr_supported(&const_field.value) {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!(
                            "const initializer for `{}.{}` uses unsupported syntax; function calls and effectful constructs are not supported yet",
                            def.name.node, const_field.name.node
                        ),
                    )
                    .at(SourceLocation {
                        file_id: const_field.value.span.file.0,
                        start: const_field.value.span.start,
                        end: const_field.value.span.end,
                    }),
                );
                env.pop_scope();
                return Err(format_diagnostics(
                    "const field registration failed",
                    diagnostics,
                ));
            }
            let Some(expected) = const_types.get(&const_name) else {
                continue;
            };
            let mut ctx = InferenceContext::new();
            check_expr_in_context(
                &const_field.value,
                expected,
                Reason::TypeAscription,
                env,
                &mut ctx,
                records,
                traits,
                sum_types,
            );
            diagnostics.extend(ctx.errors().iter().cloned());
            if ctx.has_errors() {
                env.pop_scope();
                return Err(format_diagnostics(
                    "const field registration failed",
                    diagnostics,
                ));
            }
        }

        env.pop_scope();
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn typecheck_functions(
    module: &Module,
    env: &mut TypeEnv,
    records: &mut RecordRegistry,
    traits: &mut TraitRegistry,
    sum_types: &mut SumTypeRegistry,
    diagnostics: &mut Vec<Diagnostic>,
    module_path: Option<&str>,
    // Maps method_name → owner_type_name for functions lifted from type blocks (§2.8, §3.5).
    // These are registered as inherent on their nominal type rather than the module struct.
    block_method_owners: &BTreeMap<String, String>,
) -> Result<TypecheckResult, String> {
    // Pre-register all function names and effect rows so forward references
    // (including mutual recursion) resolve correctly.  This also enables
    // transitive effect inference for forward-referenced effectful callees.
    let mut placeholder_counter = u32::MAX;
    for decl in &module.declarations {
        let fn_decl = match &decl.node {
            DeclKind::Function(fn_decl) => fn_decl.clone(),
            DeclKind::ExprFn(expr_decl) => expr_decl_to_fn_decl(expr_decl),
            _ => continue,
        };
        let resolved = resolve_fn_decl_type(&fn_decl, records, sum_types);
        let ty = resolved.unwrap_or_else(|| {
            let id = placeholder_counter;
            placeholder_counter = placeholder_counter.wrapping_sub(1);
            Type::Var(kea_types::TypeVarId(id))
        });
        if has_annotation_named(&fn_decl.annotations, "unsafe") {
            env.register_unsafe_function(&fn_decl.name.node);
            if let Some(module_path) = module_path {
                env.register_module_unsafe_function(module_path, &fn_decl.name.node);
            }
        }
        // Pre-register type-block methods in their type's namespace immediately so
        // qualified calls like `Type.method()` resolve during type inference of
        // subsequent declarations (before the full registration pass runs below).
        // fn_decl.name.node is the QUALIFIED name ("Point.distance"); extract bare.
        if let Some(owner_type) = block_method_owners.get(&fn_decl.name.node) {
            let bare_name = fn_decl
                .name
                .node
                .rsplit_once('.')
                .map(|(_, m)| m)
                .unwrap_or(&fn_decl.name.node);
            if env.resolve_module_path_alias(owner_type).is_none() {
                env.register_module_alias(owner_type, owner_type);
            }
            // Register qualified name under owner's module type schemes.
            env.register_module_function(owner_type, bare_name);
            env.register_module_type_scheme_exact(owner_type, bare_name, TypeScheme::mono(ty.clone()));
            // Register inherent dispatch with BARE method name.
            env.register_inherent_method(owner_type, bare_name);
            // Only bind bare name + UMS alias for receiver methods (positional first param).
            // Static methods (no receiver) must NOT register a bare alias — it would pollute
            // the global namespace and shadow same-named stdlib functions.
            let has_receiver = fn_decl
                .params
                .first()
                .map(|p| matches!(p.label, kea_ast::ParamLabel::Positional))
                .unwrap_or(false);
            if has_receiver {
                // Bind bare name for UMS type inference (e.g. `p.distance(q)` → `Var("distance")`).
                env.bind(bare_name.to_string(), TypeScheme::mono(ty.clone()));
                // Register bare→qualified alias so HIR lowering rewrites Var("distance")→Var("Point.distance").
                env.register_block_method_alias(bare_name, &fn_decl.name.node);
                // Register signature for the bare name so labeled-arg checking works at call sites.
                let mut bare_fn = fn_decl.clone();
                bare_fn.name.node = bare_name.to_string();
                register_fn_signature(&bare_fn, env);
            }
            // Always register the qualified-name signature eagerly so that call sites
            // earlier in the declaration order (e.g. test blocks) can resolve
            // `Direction.all()` without falling back to a same-named stdlib function.
            register_fn_signature(&fn_decl, env);
        }

        env.bind(fn_decl.name.node.clone(), TypeScheme::mono(ty));

        // Also pre-register the effect row so transitive effect inference
        // sees the declared effects of forward-referenced callees.
        let effects =
            resolve_effect_annotation_simple(&fn_decl.effect_annotation, records, sum_types);
        env.set_function_effect_row(fn_decl.name.node.clone(), effects);
    }

    let mut all_expr_types = std::collections::BTreeMap::new();
    let mut all_resolved_trait_callees = std::collections::BTreeMap::new();

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
        seed_fn_where_type_params_in_context(&fn_decl, traits, &mut ctx, records, sum_types);
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

        all_expr_types.extend(ctx.resolve_expr_types());
        all_resolved_trait_callees
            .extend(ctx.take_type_annotations().resolved_trait_callees);

        if !fn_decl.where_clause.is_empty()
            && let Some(scheme) = env.lookup(&fn_decl.name.node).cloned()
        {
            let mut scheme = scheme;
            apply_where_clause(&mut scheme, &fn_decl, ctx.substitution());
            env.bind(fn_decl.name.node.clone(), scheme);
        }

        // The Lambda arm now constrains inferred effects against the
        // declared annotation via the main unifier's Rémy row unification.
        // Extract the scheme's effect row for HIR/MIR metadata.
        let effect_row = env
            .lookup(&fn_decl.name.node)
            .and_then(|scheme| match &scheme.ty {
                Type::Function(ft) => Some(ft.effects.clone()),
                _ => None,
            })
            .unwrap_or_else(EffectRow::pure);

        env.set_function_effect_row(fn_decl.name.node.clone(), effect_row);
        register_fn_signature(&fn_decl, env);

        if let Some(module_path) = module_path {
            let module_short = module_struct_name(module_path).to_string();
            if env.resolve_module_path_alias(&module_short).is_none() {
                env.register_module_alias(&module_short, module_path);
            }

            if let Some(owner_type) = block_method_owners.get(&fn_decl.name.node) {
                // Type-block method: fn_decl.name.node is the qualified name ("Point.distance").
                // Extract the bare method name ("distance") for module type scheme keys.
                let bare_name = fn_decl
                    .name
                    .node
                    .rsplit_once('.')
                    .map(|(_, m)| m)
                    .unwrap_or(&fn_decl.name.node);
                // Update the scheme in owner type's namespace now that type inference has refined it.
                if let Some(scheme) = env.lookup(&fn_decl.name.node).cloned() {
                    env.register_module_type_scheme_exact(owner_type, bare_name, scheme);
                }
                // Propagate signature and effect row to the qualified name.
                if let Some(signature) = env.function_signature(&fn_decl.name.node).cloned() {
                    env.set_function_signature(fn_decl.name.node.clone(), signature);
                }
                if let Some(effect_row) = env.function_effect_row(&fn_decl.name.node) {
                    env.set_function_effect_row(fn_decl.name.node.clone(), effect_row);
                }
                // Also register under the module path so that merge_modules_for_codegen's
                // module-path-qualified copies (e.g. "SomeModule.Point.distance") get the right
                // type when HIR lowering calls env.resolve_qualified(module_struct_name, name).
                env.register_module_function(module_path, &fn_decl.name.node);
                if let Some(scheme) = env.lookup(&fn_decl.name.node).cloned() {
                    env.register_module_type_scheme_exact(
                        module_path,
                        &fn_decl.name.node,
                        scheme,
                    );
                }
                let qname = format!("{module_path}.{}", fn_decl.name.node);
                if let Some(signature) = env.function_signature(&fn_decl.name.node).cloned() {
                    env.set_function_signature(qname.clone(), signature);
                }
                if let Some(effect_row) = env.function_effect_row(&fn_decl.name.node) {
                    env.set_function_effect_row(qname, effect_row);
                }
            } else {
                // Normal file-scope function: register on the module struct.
                env.register_module_function(module_path, &fn_decl.name.node);
                if let Some(scheme) = env.lookup(&fn_decl.name.node).cloned() {
                    env.register_module_type_scheme_exact(module_path, &fn_decl.name.node, scheme);
                }
                if !fn_decl.name.node.contains('.') {
                    env.register_inherent_method(&module_short, &fn_decl.name.node);
                }
                let qualified_name = format!("{module_path}.{}", fn_decl.name.node);
                if let Some(signature) = env.function_signature(&fn_decl.name.node).cloned() {
                    env.set_function_signature(qualified_name.clone(), signature);
                }
                if let Some(effect_row) = env.function_effect_row(&fn_decl.name.node) {
                    env.set_function_effect_row(qualified_name, effect_row);
                }
            }
        }
    }

    Ok((all_expr_types, all_resolved_trait_callees))
}

/// Try to build a concrete `Type::Function` from a function declaration's
/// annotations, including the effect row.  Returns `None` if any param or the
/// return type is unannotated or uses an unresolvable type name.
fn resolve_fn_decl_type(
    fn_decl: &FnDecl,
    records: &RecordRegistry,
    sum_types: &SumTypeRegistry,
) -> Option<Type> {
    let ret_ann = fn_decl.return_annotation.as_ref()?;
    let ret_ty = resolve_annotation(&ret_ann.node, records, Some(sum_types))?;

    let mut param_types = Vec::with_capacity(fn_decl.params.len());
    for param in &fn_decl.params {
        let ann = param.annotation.as_ref()?;
        let ty = resolve_annotation(&ann.node, records, Some(sum_types))?;
        param_types.push(ty);
    }

    let effects = resolve_effect_annotation_simple(&fn_decl.effect_annotation, records, sum_types);

    Some(Type::Function(kea_types::FunctionType {
        params: param_types,
        ret: Box::new(ret_ty),
        effects,
    }))
}

/// Resolve an effect annotation to an `EffectRow` for pre-binding.
/// Falls back to `EffectRow::pure()` if the annotation is absent or can't be
/// fully resolved (e.g. uses effect variables).
fn resolve_effect_annotation_simple(
    ann: &Option<Spanned<kea_ast::EffectAnnotation>>,
    records: &RecordRegistry,
    sum_types: &SumTypeRegistry,
) -> kea_types::EffectRow {
    use kea_ast::EffectAnnotation;
    let Some(spanned) = ann else {
        return kea_types::EffectRow::pure();
    };
    match &spanned.node {
        EffectAnnotation::Pure => kea_types::EffectRow::pure(),
        EffectAnnotation::Row(row) => {
            // Only resolve closed rows (no rest variable) for pre-binding.
            if row.rest.is_some() {
                return kea_types::EffectRow::pure();
            }
            let mut effects = Vec::new();
            for item in &row.effects {
                let payload = if let Some(ref payload_ann) = item.payload {
                    resolve_annotation(payload_ann, records, Some(sum_types)).unwrap_or(Type::Unit)
                } else {
                    Type::Unit
                };
                effects.push((kea_types::Label::new(&item.name), payload));
            }
            kea_types::EffectRow::closed(effects)
        }
        // Volatile/Impure/Var — can't resolve to a concrete row.
        _ => kea_types::EffectRow::pure(),
    }
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
        span: expr.span,
        where_clause: expr.where_clause.clone(),
    }
}

fn validate_fip_annotations(module: &Module, hir: &HirModule) -> Vec<Diagnostic> {
    #[derive(Debug, Clone)]
    struct FipFunctionSpec {
        span: Span,
        unique_param_names: BTreeSet<String>,
    }

    let mut annotated_functions: BTreeMap<String, FipFunctionSpec> = BTreeMap::new();
    for decl in &module.declarations {
        match &decl.node {
            DeclKind::Function(fn_decl) => {
                if fn_decl.annotations.iter().any(|ann| ann.name.node == "fip") {
                    let unique_param_names = fn_decl
                        .params
                        .iter()
                        .filter_map(|param| {
                            param.annotation.as_ref().and_then(|ann| {
                                is_unique_type_annotation(&ann.node)
                                    .then(|| param.name().map(str::to_string))
                                    .flatten()
                            })
                        })
                        .collect::<BTreeSet<_>>();
                    annotated_functions
                        .entry(fn_decl.name.node.clone())
                        .or_insert(FipFunctionSpec {
                            span: fn_decl.name.span,
                            unique_param_names,
                        });
                }
            }
            DeclKind::ExprFn(expr_decl) => {
                if expr_decl
                    .annotations
                    .iter()
                    .any(|ann| ann.name.node == "fip")
                {
                    let unique_param_names = expr_decl
                        .params
                        .iter()
                        .filter_map(|param| {
                            param.annotation.as_ref().and_then(|ann| {
                                is_unique_type_annotation(&ann.node)
                                    .then(|| param.name().map(str::to_string))
                                    .flatten()
                            })
                        })
                        .collect::<BTreeSet<_>>();
                    annotated_functions
                        .entry(expr_decl.name.node.clone())
                        .or_insert(FipFunctionSpec {
                            span: expr_decl.name.span,
                            unique_param_names,
                        });
                }
            }
            _ => {}
        }
    }
    if annotated_functions.is_empty() {
        return Vec::new();
    }

    let mir = lower_hir_module_with_config(hir, &MirLoweringConfig::jit());
    let pass_stats = collect_pass_stats(&mir);
    let stats_by_name = pass_stats
        .per_function
        .iter()
        .map(|stats| (stats.function.as_str(), stats))
        .collect::<BTreeMap<_, _>>();
    let mut safe_handoff_callees = collect_safe_unique_forwarders(hir, &mir);
    let mut safe_higher_order_handoff_callees =
        collect_safe_unique_higher_order_forwarders(hir, &mir);
    let import_aliases = collect_import_aliases(module);
    extend_safe_forwarders_with_import_aliases(&mut safe_handoff_callees, &import_aliases);
    extend_safe_higher_order_forwarders_with_import_aliases(
        &mut safe_higher_order_handoff_callees,
        &import_aliases,
    );

    let mut diagnostics = Vec::new();
    for (name, fip_spec) in annotated_functions {
        let span = fip_spec.span;
        let mir_function = mir.functions.iter().find(|function| function.name == name);
        let Some(stats) = stats_by_name.get(name.as_str()) else {
            diagnostics.push(
                Diagnostic::error(
                    Category::TypeError,
                    format!("`@fip` function `{name}` could not be verified (missing MIR stats)"),
                )
                .at(SourceLocation {
                    file_id: span.file.0,
                    start: span.start,
                    end: span.end,
                })
                .with_help(
                    "the bootstrap verifier only supports named functions that lower to MIR one-to-one."
                        .to_string(),
                ),
            );
            continue;
        };

        let profile = mir_function
            .map(collect_fip_mir_profile)
            .unwrap_or_default();
        let hir_function = find_hir_function_by_name(hir, &name);
        let flow = hir_function
            .map(|function| {
                let mut aliases = BTreeMap::new();
                for root in &fip_spec.unique_param_names {
                    aliases.insert(root.clone(), root.clone());
                }
                analyze_hir_unique_flow_function(
                    function,
                    &aliases,
                    &safe_handoff_callees,
                    &safe_higher_order_handoff_callees,
                )
            })
            .unwrap_or_default();
        let raw_hir_expr_count = hir_function
            .map(|function| count_raw_hir_expr_nodes(&function.body))
            .unwrap_or(0);
        let call_boundary_summary = hir_function
            .map(|function| {
                let local_bindings = hir_function_param_bindings(function);
                collect_fip_call_boundary_issues(
                    &function.body,
                    &local_bindings,
                    &safe_handoff_callees,
                    &safe_higher_order_handoff_callees,
                    5,
                )
            })
            .unwrap_or_default();
        let mir_unique_flow = match (mir_function, hir_function) {
            (Some(mir_fn), Some(hir_fn)) => {
                collect_mir_unique_flow_summary(mir_fn, hir_fn, &fip_spec.unique_param_names)
            }
            _ => MirUniqueFlowSummary::default(),
        };
        let mut unique_flow_issues = Vec::new();
        for root in &fip_spec.unique_param_names {
            let move_boundary_count = mir_unique_flow
                .move_boundary_counts
                .get(root)
                .copied()
                .unwrap_or(0);
            let freeze_boundary_count = mir_unique_flow
                .freeze_boundary_counts
                .get(root)
                .copied()
                .unwrap_or(0);
            match flow.ref_counts.get(root).copied().unwrap_or(0) {
                0 => unique_flow_issues.push(format!(
                    "Unique parameter `{root}` is never referenced in function body (expected exactly-once consume/forward)"
                )),
                n if n > 1 => {
                    if move_boundary_count > 0 || freeze_boundary_count > 0 {
                        unique_flow_issues.push(format!(
                            "Unique parameter `{root}` is referenced {n} times on one control-flow path after explicit ownership transitions (Move={move_boundary_count}, Freeze={freeze_boundary_count}); this looks like a double handoff in a mixed alias/transform path"
                        ));
                    } else {
                        unique_flow_issues.push(format!(
                            "Unique parameter `{root}` is referenced {n} times on one control-flow path; @fip currently requires a single ownership handoff per path"
                        ));
                    }
                }
                _ => {}
            }
            let call_escape_count = flow.call_escape_counts.get(root).copied().unwrap_or(0);
            if call_escape_count > 0 {
                if move_boundary_count > 0 || freeze_boundary_count > 0 {
                    unique_flow_issues.push(format!(
                        "Unique parameter `{root}` escapes through {call_escape_count} call argument(s) despite explicit ownership transitions (Move={move_boundary_count}, Freeze={freeze_boundary_count}); @fip call-boundary ownership proofs are not yet supported"
                    ));
                } else {
                    unique_flow_issues.push(format!(
                        "Unique parameter `{root}` escapes through {call_escape_count} call argument(s); @fip call-boundary ownership proofs are not yet supported"
                    ));
                }
            }
        }
        let mut failures = Vec::new();
        if profile.disallowed_alloc_count > 0 {
            failures.push(format!(
                "disallowed_alloc_count={}",
                profile.disallowed_alloc_count
            ));
        }
        if profile.retain_count > 0 {
            failures.push(format!("retain_count={}", profile.retain_count));
        }
        if profile.explicit_release_count > 0 {
            failures.push(format!(
                "explicit_release_count={}",
                profile.explicit_release_count
            ));
        }
        if profile.reuse_token_consumed_count > profile.reuse_token_produced_count {
            failures.push(format!(
                "reuse_token_flow={} consumed > {} produced",
                profile.reuse_token_consumed_count, profile.reuse_token_produced_count
            ));
        }
        if stats.trmc_candidate_count > 0 {
            failures.push(format!(
                "trmc_candidate_count={}",
                stats.trmc_candidate_count
            ));
        }
        if !unique_flow_issues.is_empty() {
            failures.push(format!(
                "unique_flow_violations={}",
                unique_flow_issues.len()
            ));
        }
        if raw_hir_expr_count > 0 {
            failures.push(format!("raw_hir_expr_count={raw_hir_expr_count}"));
        }
        if call_boundary_summary.total_unsupported_calls > 0 {
            failures.push(format!(
                "unsupported_call_boundaries={}",
                call_boundary_summary.total_unsupported_calls
            ));
        }

        if !failures.is_empty() {
            let mut help_parts = vec![
                "expected no disallowed heap allocation ops, no retain/explicit release ops, valid reuse-token flow, and no remaining TRMC candidates after MIR lowering."
                    .to_string(),
            ];
            if let Some(function) = mir_function {
                let sites = collect_fip_offending_sites(function, 5);
                if !sites.is_empty() {
                    help_parts.push(format!("first offending MIR sites:\n{}", sites.join("\n")));
                }
            }
            if !unique_flow_issues.is_empty() {
                let lines = unique_flow_issues
                    .iter()
                    .take(5)
                    .map(|issue| format!("- {issue}"))
                    .collect::<Vec<_>>();
                help_parts.push(format!(
                    "unique ownership flow issues:\n{}",
                    lines.join("\n")
                ));
            }
            if raw_hir_expr_count > 0 {
                help_parts.push(format!(
                    "function body contains {raw_hir_expr_count} raw HIR fallback expression node(s); @fip verification only runs on fully lowered HIR."
                ));
            }
            if call_boundary_summary.total_unsupported_calls > 0 {
                let lines = call_boundary_summary
                    .sites
                    .iter()
                    .map(|site| {
                        let count = call_boundary_summary
                            .site_counts
                            .get(site)
                            .copied()
                            .unwrap_or(1);
                        if count > 1 {
                            format!("- {site} ({count} occurrences)")
                        } else {
                            format!("- {site}")
                        }
                    })
                    .collect::<Vec<_>>();
                help_parts.push(format!(
                    "unsupported cross-function call boundaries ({}):\n{}\n\n@fip currently allows only verified single-handoff forwarder calls across function boundaries.",
                    call_boundary_summary.total_unsupported_calls,
                    lines.join("\n")
                ));
            }
            diagnostics.push(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "`@fip` verification failed for `{name}` ({})",
                        failures.join(", ")
                    ),
                )
                .at(SourceLocation {
                    file_id: span.file.0,
                    start: span.start,
                    end: span.end,
                })
                .with_help(help_parts.join("\n\n")),
            );
        }
    }

    diagnostics
}

#[derive(Debug, Clone, Default)]
struct FipMirProfile {
    disallowed_alloc_count: usize,
    retain_count: usize,
    explicit_release_count: usize,
    reuse_token_produced_count: usize,
    reuse_token_consumed_count: usize,
    call_count: usize,
}

fn collect_fip_mir_profile(function: &kea_mir::MirFunction) -> FipMirProfile {
    let mut profile = FipMirProfile::default();
    for block in &function.blocks {
        for inst in &block.instructions {
            match inst {
                kea_mir::MirInst::Call { .. } => profile.call_count += 1,
                kea_mir::MirInst::Retain { .. } => profile.retain_count += 1,
                kea_mir::MirInst::Release { .. } => profile.explicit_release_count += 1,
                kea_mir::MirInst::ReuseToken { .. } => profile.reuse_token_produced_count += 1,
                kea_mir::MirInst::RecordInitFromToken { .. }
                | kea_mir::MirInst::SumInitFromToken { .. } => {
                    profile.reuse_token_consumed_count += 1
                }
                kea_mir::MirInst::ClosureInit { captures, .. } if captures.is_empty() => {}
                kea_mir::MirInst::RecordInit { .. }
                | kea_mir::MirInst::SumInit { .. }
                | kea_mir::MirInst::ClosureInit { .. }
                | kea_mir::MirInst::CowUpdate { .. }
                | kea_mir::MirInst::StateCellNew { .. } => profile.disallowed_alloc_count += 1,
                _ => {}
            }
        }
    }
    profile
}

fn mir_profile_is_non_allocating_forwarder(profile: &FipMirProfile) -> bool {
    profile.disallowed_alloc_count == 0
        && profile.retain_count == 0
        && profile.explicit_release_count == 0
        && profile.reuse_token_consumed_count <= profile.reuse_token_produced_count
}

fn is_unique_type_annotation(annotation: &TypeAnnotation) -> bool {
    match annotation {
        TypeAnnotation::Named(name) => name == "Unique",
        TypeAnnotation::Applied(name, args) => {
            name == "Unique" || args.iter().any(is_unique_type_annotation)
        }
        _ => false,
    }
}

#[derive(Debug, Clone, Default)]
struct HirUniqueFlowSummary {
    ref_counts: BTreeMap<String, usize>,
    call_escape_counts: BTreeMap<String, usize>,
    result_alias_root: Option<String>,
}

#[derive(Debug, Clone, Default)]
struct MirUniqueFlowSummary {
    move_boundary_counts: BTreeMap<String, usize>,
    freeze_boundary_counts: BTreeMap<String, usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SafeHigherOrderForwarder {
    unique_arg_index: usize,
    forwarder_arg_index: usize,
}

fn matches_higher_order_forwarder_body(
    expr: &HirExpr,
    forwarder_param_name: &str,
    unique_param_name: &str,
) -> bool {
    fn contains_call(expr: &HirExpr) -> bool {
        match &expr.kind {
            HirExprKind::Call { .. } => true,
            HirExprKind::Lit(_) | HirExprKind::Var(_) | HirExprKind::Raw(_) => false,
            HirExprKind::Unary { operand, .. } => contains_call(operand),
            HirExprKind::Binary { left, right, .. } => contains_call(left) || contains_call(right),
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                contains_call(condition)
                    || contains_call(then_branch)
                    || else_branch.as_ref().is_some_and(|branch| contains_call(branch))
            }
            HirExprKind::Let { value, .. } => contains_call(value),
            HirExprKind::Block(exprs) | HirExprKind::Tuple(exprs) => {
                exprs.iter().any(contains_call)
            }
            HirExprKind::Lambda { body, .. } => contains_call(body),
            HirExprKind::RecordLit { fields, .. } | HirExprKind::RecordUpdate { fields, .. } => {
                fields.iter().any(|(_, field_expr)| contains_call(field_expr))
            }
            HirExprKind::FieldAccess { expr, .. } | HirExprKind::SumPayloadAccess { expr, .. } => {
                contains_call(expr)
            }
            HirExprKind::SumConstructor { fields, .. } => fields.iter().any(contains_call),
            HirExprKind::Catch { expr } => contains_call(expr),
            HirExprKind::Handle {
                expr,
                clauses,
                then_clause,
            } => {
                contains_call(expr)
                    || clauses.iter().any(|clause| contains_call(&clause.body))
                    || then_clause.as_ref().is_some_and(|then_expr| contains_call(then_expr))
            }
            HirExprKind::Resume { value } => contains_call(value),
        }
    }

    fn extract_alias_bindings_let(expr: &HirExpr) -> Option<Vec<(String, String)>> {
        match &expr.kind {
            HirExprKind::Let { pattern, value } => match (pattern, &value.kind) {
                (kea_hir::HirPattern::Var(binding_name), HirExprKind::Var(source_name)) => {
                    Some(vec![(binding_name.clone(), source_name.clone())])
                }
                (kea_hir::HirPattern::Raw(PatternKind::Tuple(patterns)), HirExprKind::Tuple(values))
                    if patterns.len() == values.len() =>
                {
                    let mut aliases = Vec::with_capacity(patterns.len());
                    for (pattern, value) in patterns.iter().zip(values.iter()) {
                        let PatternKind::Var(binding_name) = &pattern.node else {
                            return None;
                        };
                        let HirExprKind::Var(source_name) = &value.kind else {
                            return None;
                        };
                        aliases.push((binding_name.clone(), source_name.clone()));
                    }
                    Some(aliases)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn absorb_alias_bindings(
        bindings: &[(String, String)],
        unique_aliases: &mut BTreeSet<String>,
        forwarder_aliases: Option<&mut BTreeSet<String>>,
    ) {
        let mut forwarder_aliases = forwarder_aliases;
        for (binding_name, source_name) in bindings {
            if unique_aliases.contains(source_name) {
                unique_aliases.insert(binding_name.clone());
            }
            if let Some(forwarder_aliases) = forwarder_aliases.as_deref_mut()
                && forwarder_aliases.contains(source_name)
            {
                forwarder_aliases.insert(binding_name.clone());
            }
        }
    }

    fn matches_forwarder_call(
        expr: &HirExpr,
        allowed_forwarder_aliases: &BTreeSet<String>,
        allowed_unique_aliases: &BTreeSet<String>,
    ) -> bool {
        match &expr.kind {
            HirExprKind::Call { func, args } if args.len() == 1 => {
                matches!(&func.kind, HirExprKind::Var(name) if allowed_forwarder_aliases.contains(name))
                    && matches!(&args[0].kind, HirExprKind::Var(name) if allowed_unique_aliases.contains(name))
            }
            _ => false,
        }
    }

    fn matches_shape(
        expr: &HirExpr,
        forwarder_aliases: &BTreeSet<String>,
        unique_aliases: &BTreeSet<String>,
    ) -> bool {
        fn matches_alias_shape(expr: &HirExpr, aliases: &BTreeSet<String>) -> bool {
            match &expr.kind {
                HirExprKind::Var(name) => aliases.contains(name),
                HirExprKind::Block(exprs) if !exprs.is_empty() => {
                    let mut aliases = aliases.clone();
                    for (index, item) in exprs.iter().enumerate() {
                        let is_last = index + 1 == exprs.len();
                        if is_last {
                            return matches_alias_shape(item, &aliases);
                        }

                        if let Some(bindings) = extract_alias_bindings_let(item) {
                            for (binding_name, source_name) in &bindings {
                                if aliases.contains(source_name) {
                                    aliases.insert(binding_name.clone());
                                }
                            }
                            // Benign alias lets on unrelated params are
                            // allowed in call-free prelude paths.
                            continue;
                        }

                        match &item.kind {
                            HirExprKind::Let { pattern, value }
                                if matches!(pattern, kea_hir::HirPattern::Var(_)) =>
                            {
                                if matches_alias_shape(value, &aliases) {
                                    let binding_name = match pattern {
                                        kea_hir::HirPattern::Var(name) => name,
                                        _ => unreachable!("guarded by match"),
                                    };
                                    aliases.insert(binding_name.to_string());
                                    continue;
                                }
                                if !contains_call(value) {
                                    continue;
                                }
                                return false;
                            }
                            _ => return false,
                        }
                    }
                    false
                }
                HirExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    let Some(else_branch) = else_branch.as_ref() else {
                        return false;
                    };
                    !contains_call(condition)
                        && matches_alias_shape(then_branch, aliases)
                        && matches_alias_shape(else_branch, aliases)
                }
                _ => false,
            }
        }

        match &expr.kind {
            HirExprKind::Call { .. } => {
                matches_forwarder_call(expr, forwarder_aliases, unique_aliases)
            }
            HirExprKind::Block(exprs) if !exprs.is_empty() => {
                let mut forwarder_aliases = forwarder_aliases.clone();
                let mut unique_aliases = unique_aliases.clone();
                let mut result_aliases: Option<BTreeSet<String>> = None;
                for (index, item) in exprs.iter().enumerate() {
                    let is_last = index + 1 == exprs.len();
                    if result_aliases.is_none() {
                        if is_last {
                            return matches_shape(item, &forwarder_aliases, &unique_aliases);
                        }

                        if let Some(bindings) = extract_alias_bindings_let(item) {
                            absorb_alias_bindings(
                                &bindings,
                                &mut unique_aliases,
                                Some(&mut forwarder_aliases),
                            );
                            // Benign passthrough alias lets on unrelated params
                            // are allowed before the unique handoff call.
                            continue;
                        }

                        match &item.kind {
                            HirExprKind::Let { pattern, value }
                                if matches!(pattern, kea_hir::HirPattern::Var(_)) =>
                            {
                                if matches_alias_shape(value, &unique_aliases) {
                                    let binding_name = match pattern {
                                        kea_hir::HirPattern::Var(name) => name,
                                        _ => unreachable!("guarded by match"),
                                    };
                                    unique_aliases.insert(binding_name.to_string());
                                    continue;
                                }
                                if matches_alias_shape(value, &forwarder_aliases) {
                                    let binding_name = match pattern {
                                        kea_hir::HirPattern::Var(name) => name,
                                        _ => unreachable!("guarded by match"),
                                    };
                                    forwarder_aliases.insert(binding_name.to_string());
                                    continue;
                                }
                                if matches_shape(value, &forwarder_aliases, &unique_aliases) {
                                    let binding_name = match pattern {
                                        kea_hir::HirPattern::Var(name) => name,
                                        _ => unreachable!("guarded by match"),
                                    };
                                    result_aliases = Some(BTreeSet::from([binding_name.clone()]));
                                    continue;
                                }
                                // Benign call-free setup lets are allowed before the
                                // single forward handoff.
                                if !contains_call(value) {
                                    continue;
                                }
                                return false;
                            }
                            _ => return false,
                        }
                    }

                    let Some(result_aliases) = result_aliases.as_mut() else {
                        unreachable!("guarded by is_none check");
                    };

                    if is_last {
                        return matches_alias_shape(item, result_aliases);
                    }

                    match &item.kind {
                        HirExprKind::Let { pattern, value }
                            if matches!(pattern, kea_hir::HirPattern::Var(_)) =>
                        {
                            if matches_alias_shape(value, result_aliases) {
                                let binding_name = match pattern {
                                    kea_hir::HirPattern::Var(name) => name,
                                    _ => unreachable!("guarded by match"),
                                };
                                result_aliases.insert(binding_name.to_string());
                                continue;
                            }
                            // Benign call-free lets are allowed after forward-call
                            // result shaping as long as they introduce no calls.
                            if !contains_call(value) {
                                continue;
                            }
                            return false;
                        }
                        _ => return false,
                    }
                }
                false
            }
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let Some(else_branch) = else_branch.as_ref() else {
                    return false;
                };
                if contains_call(condition) {
                    return false;
                }
                let then_forward = matches_shape(then_branch, forwarder_aliases, unique_aliases);
                let else_forward = matches_shape(else_branch, forwarder_aliases, unique_aliases);
                let then_passthrough = matches_alias_shape(then_branch, unique_aliases);
                let else_passthrough = matches_alias_shape(else_branch, unique_aliases);
                (then_forward && (else_forward || else_passthrough))
                    || (else_forward && then_passthrough)
            }
            _ => false,
        }
    }

    matches_shape(
        expr,
        &BTreeSet::from([forwarder_param_name.to_string()]),
        &BTreeSet::from([unique_param_name.to_string()]),
    )
}

fn collect_safe_unique_forwarders(
    hir: &HirModule,
    mir: &kea_mir::MirModule,
) -> BTreeMap<String, usize> {
    let mut safe = BTreeMap::new();
    let mir_profiles = mir
        .functions
        .iter()
        .map(|function| (function.name.clone(), collect_fip_mir_profile(function)))
        .collect::<BTreeMap<_, _>>();
    let mut short_name_counts = BTreeMap::new();
    for decl in &hir.declarations {
        let HirDecl::Function(function) = decl else {
            continue;
        };
        let short = function
            .name
            .rsplit('.')
            .next()
            .unwrap_or(function.name.as_str())
            .to_string();
        *short_name_counts.entry(short).or_default() += 1usize;
    }
    let no_safe_handoffs = BTreeMap::new();

    for decl in &hir.declarations {
        let HirDecl::Function(function) = decl else {
            continue;
        };
        let candidate_roots = function
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| param.name.clone().map(|name| (name, idx)))
            .collect::<Vec<_>>();

        let mut safe_arg_index = None;
        for (root, param_index) in candidate_roots {
            let aliases = BTreeMap::from([(root.clone(), root.clone())]);
            let no_safe_higher_order_handoffs = BTreeMap::new();
            let flow = analyze_hir_unique_flow_function(
                function,
                &aliases,
                &no_safe_handoffs,
                &no_safe_higher_order_handoffs,
            );
            let ref_count = flow.ref_counts.get(&root).copied().unwrap_or(0);
            let call_escape_count = flow.call_escape_counts.get(&root).copied().unwrap_or(0);
            if ref_count == 1
                && call_escape_count == 0
                && flow.result_alias_root.as_deref() == Some(root.as_str())
            {
                safe_arg_index = Some(param_index);
                break;
            }
        }
        let Some(safe_arg_index) = safe_arg_index else {
            continue;
        };
        let Some(profile) = mir_profiles.get(&function.name) else {
            continue;
        };
        // Safe direct-call boundary proofs must be zero-overhead handoffs:
        // no hidden alloc/retain/release churn and no nested calls.
        if !mir_profile_is_non_allocating_forwarder(profile) || profile.call_count > 0 {
            continue;
        }

        safe.insert(function.name.clone(), safe_arg_index);
        let short = function
            .name
            .rsplit('.')
            .next()
            .unwrap_or(function.name.as_str());
        if short_name_counts.get(short).copied().unwrap_or(0) == 1 {
            safe.insert(short.to_string(), safe_arg_index);
        }
    }

    safe
}

fn collect_safe_unique_higher_order_forwarders(
    hir: &HirModule,
    mir: &kea_mir::MirModule,
) -> BTreeMap<String, SafeHigherOrderForwarder> {
    let mut safe = BTreeMap::new();
    let mir_profiles = mir
        .functions
        .iter()
        .map(|function| (function.name.clone(), collect_fip_mir_profile(function)))
        .collect::<BTreeMap<_, _>>();
    let mut short_name_counts = BTreeMap::new();
    for decl in &hir.declarations {
        let HirDecl::Function(function) = decl else {
            continue;
        };
        let short = function
            .name
            .rsplit('.')
            .next()
            .unwrap_or(function.name.as_str())
            .to_string();
        *short_name_counts.entry(short).or_default() += 1usize;
    }

    for decl in &hir.declarations {
        let HirDecl::Function(function) = decl else {
            continue;
        };
        if function.params.len() < 2 {
            continue;
        }

        let mut matched = None;
        for (unique_index, unique_param) in function.params.iter().enumerate() {
            let Some(expected_unique_name) = unique_param.name.as_ref() else {
                continue;
            };

            for (forwarder_index, forwarder_param) in function.params.iter().enumerate() {
                if forwarder_index == unique_index {
                    continue;
                }
                let Some(expected_forwarder_name) = forwarder_param.name.as_ref() else {
                    continue;
                };
                if !matches_higher_order_forwarder_body(
                    &function.body,
                    expected_forwarder_name,
                    expected_unique_name,
                ) {
                    continue;
                }
                matched = Some(SafeHigherOrderForwarder {
                    unique_arg_index: unique_index,
                    forwarder_arg_index: forwarder_index,
                });
                break;
            }
            if matched.is_some() {
                break;
            }
        }

        let Some(spec) = matched else {
            continue;
        };
        let Some(profile) = mir_profiles.get(&function.name) else {
            continue;
        };
        // Higher-order wrappers can contain a forward call, but must remain
        // allocation-free and retain/release neutral for transitive @fip safety.
        if !mir_profile_is_non_allocating_forwarder(profile) {
            continue;
        }
        safe.insert(function.name.clone(), spec);
        let short = function
            .name
            .rsplit('.')
            .next()
            .unwrap_or(function.name.as_str());
        if short_name_counts.get(short).copied().unwrap_or(0) == 1 {
            safe.insert(short.to_string(), spec);
        }
    }

    safe
}

fn add_ref_counts(dst: &mut BTreeMap<String, usize>, src: &BTreeMap<String, usize>) {
    for (name, count) in src {
        *dst.entry(name.clone()).or_default() += *count;
    }
}

fn max_ref_counts(
    left: &BTreeMap<String, usize>,
    right: &BTreeMap<String, usize>,
) -> BTreeMap<String, usize> {
    let keys = left
        .keys()
        .chain(right.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut merged = BTreeMap::new();
    for key in keys {
        let max_count = left
            .get(&key)
            .copied()
            .unwrap_or(0)
            .max(right.get(&key).copied().unwrap_or(0));
        merged.insert(key, max_count);
    }
    merged
}

fn find_hir_function_by_name<'a>(hir: &'a HirModule, name: &str) -> Option<&'a HirFunction> {
    for decl in &hir.declarations {
        let HirDecl::Function(function) = decl else {
            continue;
        };
        if function.name == name || function.name.ends_with(&format!(".{name}")) {
            return Some(function);
        }
    }
    None
}

fn resolve_unique_root(name: &str, aliases: &BTreeMap<String, String>) -> Option<String> {
    aliases.get(name).cloned()
}

fn hir_call_crosses_ownership_boundary(func: &HirExpr) -> bool {
    !matches!(func.kind, HirExprKind::Lambda { .. })
}

fn hir_callable_root_name(func: &HirExpr) -> Option<String> {
    match &func.kind {
        HirExprKind::Var(name) => Some(name.clone()),
        HirExprKind::FieldAccess { expr, .. } => hir_callable_root_name(expr),
        _ => None,
    }
}

fn hir_callable_name(func: &HirExpr) -> Option<String> {
    match &func.kind {
        HirExprKind::Var(name) => Some(name.clone()),
        HirExprKind::FieldAccess { expr, field } => {
            let owner = hir_callable_name(expr)?;
            Some(format!("{owner}.{field}"))
        }
        _ => None,
    }
}

fn local_binding_lookup_key(name: &str) -> &str {
    // HIR can carry monomorphized helper suffixes (for example
    // `name$m0$Dyn`) on locally-bound callable values. Local binding scopes
    // are source-named, so normalize to the source prefix before shadowing
    // checks.
    name.split('$').next().unwrap_or(name)
}

fn hir_call_safe_unique_handoff_arg_index(
    func: &HirExpr,
    args: &[HirExpr],
    safe_handoff_callees: &BTreeMap<String, usize>,
    safe_higher_order_handoff_callees: &BTreeMap<String, SafeHigherOrderForwarder>,
    local_bindings: &BTreeSet<String>,
) -> Option<usize> {
    if args.is_empty() {
        return None;
    }
    if let Some(root) = hir_callable_root_name(func)
        && local_bindings.contains(local_binding_lookup_key(&root))
    {
        return None;
    }
    let name = hir_callable_name(func)?;
    let short_name = name.rsplit('.').next().unwrap_or(name.as_str());
    let safe_direct_handoff_arg_index = safe_handoff_callees
        .get(&name)
        .copied()
        .or_else(|| safe_handoff_callees.get(short_name).copied());
    if let Some(arg_index) = safe_direct_handoff_arg_index
        && arg_index < args.len()
    {
        return Some(arg_index);
    }
    let spec = safe_higher_order_handoff_callees
        .get(&name)
        .copied()
        .or_else(|| safe_higher_order_handoff_callees.get(short_name).copied());
    if let Some(spec) = spec {
        // When we have a body-derived higher-order wrapper spec for this callee,
        // do not fall back to shape-only callable-type inference if the spec
        // doesn't validate at this call site. Falling back can incorrectly accept
        // calls where a different safe function argument is present but the wrapper
        // body forwards through an unresolved/local function slot.
        return hir_call_safe_unique_handoff_arg_index_from_spec(
            &spec,
            args,
            safe_handoff_callees,
            local_bindings,
        );
    }
    None
}

fn hir_call_safe_unique_handoff_arg_index_from_spec(
    spec: &SafeHigherOrderForwarder,
    args: &[HirExpr],
    safe_handoff_callees: &BTreeMap<String, usize>,
    local_bindings: &BTreeSet<String>,
) -> Option<usize> {
    if spec.unique_arg_index >= args.len() || spec.forwarder_arg_index >= args.len() {
        return None;
    }
    let forwarder_expr = &args[spec.forwarder_arg_index];
    if let Some(root) = hir_callable_root_name(forwarder_expr)
        && local_bindings.contains(local_binding_lookup_key(&root))
    {
        return None;
    }
    let forwarder_name = hir_callable_name(forwarder_expr)?;
    let forwarder_short_name = forwarder_name
        .rsplit('.')
        .next()
        .unwrap_or(forwarder_name.as_str());
    let safe_forwarder_arg_index = safe_handoff_callees
        .get(&forwarder_name)
        .copied()
        .or_else(|| safe_handoff_callees.get(forwarder_short_name).copied());
    (safe_forwarder_arg_index == Some(0)).then_some(spec.unique_arg_index)
}

fn hir_function_param_bindings(function: &HirFunction) -> BTreeSet<String> {
    function
        .params
        .iter()
        .filter_map(|param| param.name.clone())
        .collect()
}

fn extend_hir_pattern_bindings(pattern: &kea_hir::HirPattern, out: &mut BTreeSet<String>) {
    match pattern {
        kea_hir::HirPattern::Var(name) => {
            out.insert(name.clone());
        }
        kea_hir::HirPattern::Raw(pattern) => {
            let mut names = HashSet::new();
            collect_pattern_bindings_pub(pattern, &mut names);
            out.extend(names);
        }
    }
}

#[derive(Debug, Clone, Default)]
struct FipCallBoundaryIssues {
    total_unsupported_calls: usize,
    sites: Vec<String>,
    site_counts: BTreeMap<String, usize>,
}

fn merge_fip_call_boundary_issues(
    dst: &mut FipCallBoundaryIssues,
    src: FipCallBoundaryIssues,
    site_limit: usize,
) {
    dst.total_unsupported_calls += src.total_unsupported_calls;
    for (site, count) in src.site_counts {
        *dst.site_counts.entry(site).or_default() += count;
    }
    for site in src.sites {
        if dst.sites.contains(&site) {
            continue;
        }
        if dst.sites.len() >= site_limit {
            break;
        }
        dst.sites.push(site);
    }
}

fn record_fip_call_boundary_issue(
    issues: &mut FipCallBoundaryIssues,
    site: String,
    site_limit: usize,
) {
    issues.total_unsupported_calls += 1;
    let count = issues.site_counts.entry(site.clone()).or_default();
    *count += 1;
    if *count == 1 && issues.sites.len() < site_limit {
        issues.sites.push(site);
    }
}

fn collect_fip_call_boundary_issues(
    expr: &HirExpr,
    local_bindings: &BTreeSet<String>,
    safe_handoff_callees: &BTreeMap<String, usize>,
    safe_higher_order_handoff_callees: &BTreeMap<String, SafeHigherOrderForwarder>,
    site_limit: usize,
) -> FipCallBoundaryIssues {
    fn walk(
        expr: &HirExpr,
        local_bindings: &BTreeSet<String>,
        safe_handoff_callees: &BTreeMap<String, usize>,
        safe_higher_order_handoff_callees: &BTreeMap<String, SafeHigherOrderForwarder>,
        site_limit: usize,
    ) -> FipCallBoundaryIssues {
        match &expr.kind {
            HirExprKind::Lit(_) | HirExprKind::Var(_) | HirExprKind::Raw(_) => {
                FipCallBoundaryIssues::default()
            }
            HirExprKind::Unary { operand, .. } => walk(
                operand,
                local_bindings,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                site_limit,
            ),
            HirExprKind::Binary { left, right, .. } => {
                let mut issues = walk(
                    left,
                    local_bindings,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    site_limit,
                );
                merge_fip_call_boundary_issues(
                    &mut issues,
                    walk(
                        right,
                        local_bindings,
                        safe_handoff_callees,
                        safe_higher_order_handoff_callees,
                        site_limit,
                    ),
                    site_limit,
                );
                issues
            }
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let mut issues = walk(
                    condition,
                    local_bindings,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    site_limit,
                );
                merge_fip_call_boundary_issues(
                    &mut issues,
                    walk(
                        then_branch,
                        local_bindings,
                        safe_handoff_callees,
                        safe_higher_order_handoff_callees,
                        site_limit,
                    ),
                    site_limit,
                );
                if let Some(else_expr) = else_branch {
                    merge_fip_call_boundary_issues(
                        &mut issues,
                        walk(
                            else_expr,
                            local_bindings,
                            safe_handoff_callees,
                            safe_higher_order_handoff_callees,
                            site_limit,
                        ),
                        site_limit,
                    );
                }
                issues
            }
            HirExprKind::Call { func, args } => {
                let mut issues = walk(
                    func,
                    local_bindings,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    site_limit,
                );
                for arg in args {
                    merge_fip_call_boundary_issues(
                        &mut issues,
                        walk(
                            arg,
                            local_bindings,
                            safe_handoff_callees,
                            safe_higher_order_handoff_callees,
                            site_limit,
                        ),
                        site_limit,
                    );
                }
                if hir_call_crosses_ownership_boundary(func)
                    && hir_call_safe_unique_handoff_arg_index(
                        func,
                        args,
                        safe_handoff_callees,
                        safe_higher_order_handoff_callees,
                        local_bindings,
                    )
                    .is_none()
                {
                    let call_name = hir_callable_name(func)
                        .unwrap_or_else(|| "<local callable>".to_string());
                    record_fip_call_boundary_issue(&mut issues, call_name, site_limit);
                }
                issues
            }
            HirExprKind::Let { value, .. } => walk(
                value,
                local_bindings,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                site_limit,
            ),
            HirExprKind::Block(exprs) => {
                let mut scoped_bindings = local_bindings.clone();
                let mut issues = FipCallBoundaryIssues::default();
                for item in exprs {
                    merge_fip_call_boundary_issues(
                        &mut issues,
                        walk(
                            item,
                            &scoped_bindings,
                            safe_handoff_callees,
                            safe_higher_order_handoff_callees,
                            site_limit,
                        ),
                        site_limit,
                    );
                    if let HirExprKind::Let { pattern, .. } = &item.kind {
                        extend_hir_pattern_bindings(pattern, &mut scoped_bindings);
                    }
                }
                issues
            }
            HirExprKind::Tuple(exprs) => {
                let mut issues = FipCallBoundaryIssues::default();
                for item in exprs {
                    merge_fip_call_boundary_issues(
                        &mut issues,
                        walk(
                            item,
                            local_bindings,
                            safe_handoff_callees,
                            safe_higher_order_handoff_callees,
                            site_limit,
                        ),
                        site_limit,
                    );
                }
                issues
            }
            HirExprKind::Lambda { params, body } => {
                let mut lambda_bindings = local_bindings.clone();
                for param in params {
                    if let Some(name) = &param.name {
                        lambda_bindings.insert(name.clone());
                    }
                }
                walk(
                    body,
                    &lambda_bindings,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    site_limit,
                )
            }
            HirExprKind::RecordLit { fields, .. } => {
                let mut issues = FipCallBoundaryIssues::default();
                for (_, field_expr) in fields {
                    merge_fip_call_boundary_issues(
                        &mut issues,
                        walk(
                            field_expr,
                            local_bindings,
                            safe_handoff_callees,
                            safe_higher_order_handoff_callees,
                            site_limit,
                        ),
                        site_limit,
                    );
                }
                issues
            }
            HirExprKind::RecordUpdate { base, fields, .. } => {
                let mut issues = walk(
                    base,
                    local_bindings,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    site_limit,
                );
                for (_, field_expr) in fields {
                    merge_fip_call_boundary_issues(
                        &mut issues,
                        walk(
                            field_expr,
                            local_bindings,
                            safe_handoff_callees,
                            safe_higher_order_handoff_callees,
                            site_limit,
                        ),
                        site_limit,
                    );
                }
                issues
            }
            HirExprKind::FieldAccess { expr, .. } | HirExprKind::SumPayloadAccess { expr, .. } => {
                walk(
                    expr,
                    local_bindings,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    site_limit,
                )
            }
            HirExprKind::SumConstructor { fields, .. } => {
                let mut issues = FipCallBoundaryIssues::default();
                for field_expr in fields {
                    merge_fip_call_boundary_issues(
                        &mut issues,
                        walk(
                            field_expr,
                            local_bindings,
                            safe_handoff_callees,
                            safe_higher_order_handoff_callees,
                            site_limit,
                        ),
                        site_limit,
                    );
                }
                issues
            }
            HirExprKind::Catch { expr } => walk(
                expr,
                local_bindings,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                site_limit,
            ),
            HirExprKind::Handle {
                expr,
                clauses,
                then_clause,
            } => {
                let mut issues = walk(
                    expr,
                    local_bindings,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    site_limit,
                );
                for clause in clauses {
                    let mut clause_bindings = local_bindings.clone();
                    for arg in &clause.args {
                        extend_hir_pattern_bindings(arg, &mut clause_bindings);
                    }
                    merge_fip_call_boundary_issues(
                        &mut issues,
                        walk(
                            &clause.body,
                            &clause_bindings,
                            safe_handoff_callees,
                            safe_higher_order_handoff_callees,
                            site_limit,
                        ),
                        site_limit,
                    );
                }
                if let Some(then_expr) = then_clause {
                    merge_fip_call_boundary_issues(
                        &mut issues,
                        walk(
                            then_expr,
                            local_bindings,
                            safe_handoff_callees,
                            safe_higher_order_handoff_callees,
                            site_limit,
                        ),
                        site_limit,
                    );
                }
                issues
            }
            HirExprKind::Resume { value } => walk(
                value,
                local_bindings,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                site_limit,
            ),
        }
    }

    walk(
        expr,
        local_bindings,
        safe_handoff_callees,
        safe_higher_order_handoff_callees,
        site_limit,
    )
}

fn analyze_hir_unique_flow_function(
    function: &HirFunction,
    aliases: &BTreeMap<String, String>,
    safe_handoff_callees: &BTreeMap<String, usize>,
    safe_higher_order_handoff_callees: &BTreeMap<String, SafeHigherOrderForwarder>,
) -> HirUniqueFlowSummary {
    let local_bindings = hir_function_param_bindings(function);
    analyze_hir_unique_flow_expr_scoped(
        &function.body,
        aliases,
        safe_handoff_callees,
        safe_higher_order_handoff_callees,
        &local_bindings,
    )
}

fn count_raw_hir_expr_nodes(expr: &HirExpr) -> usize {
    match &expr.kind {
        HirExprKind::Raw(_) => 1,
        HirExprKind::Lit(_) | HirExprKind::Var(_) => 0,
        HirExprKind::Unary { operand, .. } => count_raw_hir_expr_nodes(operand),
        HirExprKind::Binary { left, right, .. } => {
            count_raw_hir_expr_nodes(left) + count_raw_hir_expr_nodes(right)
        }
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut count =
                count_raw_hir_expr_nodes(condition) + count_raw_hir_expr_nodes(then_branch);
            if let Some(else_expr) = else_branch {
                count += count_raw_hir_expr_nodes(else_expr);
            }
            count
        }
        HirExprKind::Call { func, args } => {
            count_raw_hir_expr_nodes(func) + args.iter().map(count_raw_hir_expr_nodes).sum::<usize>()
        }
        HirExprKind::Let { value, .. } => count_raw_hir_expr_nodes(value),
        HirExprKind::Block(exprs) | HirExprKind::Tuple(exprs) => {
            exprs.iter().map(count_raw_hir_expr_nodes).sum()
        }
        HirExprKind::Lambda { body, .. } | HirExprKind::Catch { expr: body } => {
            count_raw_hir_expr_nodes(body)
        }
        HirExprKind::RecordLit { fields, .. } => fields
            .iter()
            .map(|(_, field_expr)| count_raw_hir_expr_nodes(field_expr))
            .sum(),
        HirExprKind::RecordUpdate { base, fields, .. } => {
            count_raw_hir_expr_nodes(base)
                + fields
                    .iter()
                    .map(|(_, field_expr)| count_raw_hir_expr_nodes(field_expr))
                    .sum::<usize>()
        }
        HirExprKind::FieldAccess { expr, .. } | HirExprKind::SumPayloadAccess { expr, .. } => {
            count_raw_hir_expr_nodes(expr)
        }
        HirExprKind::SumConstructor { fields, .. } => {
            fields.iter().map(count_raw_hir_expr_nodes).sum()
        }
        HirExprKind::Handle {
            expr,
            clauses,
            then_clause,
        } => {
            let mut count = count_raw_hir_expr_nodes(expr)
                + clauses
                    .iter()
                    .map(|clause| count_raw_hir_expr_nodes(&clause.body))
                    .sum::<usize>();
            if let Some(then_expr) = then_clause {
                count += count_raw_hir_expr_nodes(then_expr);
            }
            count
        }
        HirExprKind::Resume { value } => count_raw_hir_expr_nodes(value),
    }
}

fn analyze_hir_unique_flow_expr_scoped(
    expr: &HirExpr,
    aliases: &BTreeMap<String, String>,
    safe_handoff_callees: &BTreeMap<String, usize>,
    safe_higher_order_handoff_callees: &BTreeMap<String, SafeHigherOrderForwarder>,
    local_bindings: &BTreeSet<String>,
) -> HirUniqueFlowSummary {
    match &expr.kind {
        HirExprKind::Lit(_) => HirUniqueFlowSummary::default(),
        HirExprKind::Var(name) => {
            let mut summary = HirUniqueFlowSummary::default();
            if let Some(root) = resolve_unique_root(name, aliases) {
                *summary.ref_counts.entry(root.clone()).or_default() += 1;
                summary.result_alias_root = Some(root);
            }
            summary
        }
        HirExprKind::Binary { left, right, .. } => {
            let left_summary = analyze_hir_unique_flow_expr_scoped(
                left,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            let right_summary = analyze_hir_unique_flow_expr_scoped(
                right,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            let mut summary = HirUniqueFlowSummary::default();
            add_ref_counts(&mut summary.ref_counts, &left_summary.ref_counts);
            add_ref_counts(&mut summary.ref_counts, &right_summary.ref_counts);
            add_ref_counts(
                &mut summary.call_escape_counts,
                &left_summary.call_escape_counts,
            );
            add_ref_counts(
                &mut summary.call_escape_counts,
                &right_summary.call_escape_counts,
            );
            summary
        }
        HirExprKind::Unary { operand, .. } => analyze_hir_unique_flow_expr_scoped(
            operand,
            aliases,
            safe_handoff_callees,
            safe_higher_order_handoff_callees,
            local_bindings,
        ),
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let condition_summary = analyze_hir_unique_flow_expr_scoped(
                condition,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            let then_summary = analyze_hir_unique_flow_expr_scoped(
                then_branch,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            let else_summary = else_branch
                .as_ref()
                .map(|branch| {
                    analyze_hir_unique_flow_expr_scoped(
                        branch,
                        aliases,
                        safe_handoff_callees,
                        safe_higher_order_handoff_callees,
                        local_bindings,
                    )
                })
                .unwrap_or_default();
            let mut summary = HirUniqueFlowSummary::default();
            add_ref_counts(&mut summary.ref_counts, &condition_summary.ref_counts);
            add_ref_counts(
                &mut summary.ref_counts,
                &max_ref_counts(&then_summary.ref_counts, &else_summary.ref_counts),
            );
            add_ref_counts(
                &mut summary.call_escape_counts,
                &condition_summary.call_escape_counts,
            );
            add_ref_counts(
                &mut summary.call_escape_counts,
                &max_ref_counts(
                    &then_summary.call_escape_counts,
                    &else_summary.call_escape_counts,
                ),
            );
            summary.result_alias_root = match (
                then_summary.result_alias_root.as_ref(),
                else_summary.result_alias_root.as_ref(),
            ) {
                (Some(then_root), Some(else_root)) if then_root == else_root => {
                    Some(then_root.clone())
                }
                _ => None,
            };
            summary
        }
        HirExprKind::Call { func, args } => {
            let mut summary = analyze_hir_unique_flow_expr_scoped(
                func,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            let crosses_boundary = hir_call_crosses_ownership_boundary(func);
            let safe_handoff_arg_index = hir_call_safe_unique_handoff_arg_index(
                func,
                args,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            let mut safe_handoff_root = None;
            for (arg_index, arg) in args.iter().enumerate() {
                let arg_summary = analyze_hir_unique_flow_expr_scoped(
                    arg,
                    aliases,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    local_bindings,
                );
                add_ref_counts(&mut summary.ref_counts, &arg_summary.ref_counts);
                add_ref_counts(
                    &mut summary.call_escape_counts,
                    &arg_summary.call_escape_counts,
                );
                if safe_handoff_arg_index == Some(arg_index)
                    && safe_handoff_root.is_none()
                    && let Some(root) = arg_summary.result_alias_root.clone()
                {
                    safe_handoff_root = Some(root);
                } else if crosses_boundary && let Some(root) = arg_summary.result_alias_root {
                    *summary.call_escape_counts.entry(root).or_default() += 1;
                }
            }
            summary.result_alias_root = safe_handoff_root;
            summary
        }
        HirExprKind::Let { pattern, value } => {
            let mut summary = analyze_hir_unique_flow_expr_scoped(
                value,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            if matches!(pattern, kea_hir::HirPattern::Var(_))
                && let Some(root) = summary.result_alias_root.clone()
                && let Some(count) = summary.ref_counts.get_mut(&root)
            {
                *count = count.saturating_sub(1);
            }
            summary
        }
        HirExprKind::Block(exprs) => {
            let mut scoped_aliases = aliases.clone();
            let mut scoped_local_bindings = local_bindings.clone();
            let mut summary = HirUniqueFlowSummary::default();
            for item in exprs {
                let item_summary = analyze_hir_unique_flow_expr_scoped(
                    item,
                    &scoped_aliases,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    &scoped_local_bindings,
                );
                add_ref_counts(&mut summary.ref_counts, &item_summary.ref_counts);
                add_ref_counts(
                    &mut summary.call_escape_counts,
                    &item_summary.call_escape_counts,
                );
                if let HirExprKind::Let { pattern, .. } = &item.kind
                    && let kea_hir::HirPattern::Var(binding) = pattern
                {
                    if let Some(root) = item_summary.result_alias_root {
                        scoped_aliases.insert(binding.clone(), root);
                    } else {
                        scoped_aliases.remove(binding);
                    }
                    scoped_local_bindings.insert(binding.clone());
                    summary.result_alias_root = None;
                    continue;
                } else if let HirExprKind::Let { pattern, .. } = &item.kind {
                    // Non-var patterns still introduce local names (e.g.
                    // destructuring). Track them so ownership/call-boundary
                    // checks don't treat shadowed names as global callees.
                    extend_hir_pattern_bindings(pattern, &mut scoped_local_bindings);
                    summary.result_alias_root = None;
                    continue;
                }
                summary.result_alias_root = item_summary.result_alias_root;
            }
            summary
        }
        HirExprKind::Tuple(exprs) => {
            let mut summary = HirUniqueFlowSummary::default();
            for item in exprs {
                let item_summary = analyze_hir_unique_flow_expr_scoped(
                    item,
                    aliases,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    local_bindings,
                );
                add_ref_counts(&mut summary.ref_counts, &item_summary.ref_counts);
                add_ref_counts(
                    &mut summary.call_escape_counts,
                    &item_summary.call_escape_counts,
                );
            }
            summary
        }
        HirExprKind::Lambda { params, body } => {
            let mut lambda_local_bindings = local_bindings.clone();
            for param in params {
                if let Some(name) = &param.name {
                    lambda_local_bindings.insert(name.clone());
                }
            }
            analyze_hir_unique_flow_expr_scoped(
                body,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                &lambda_local_bindings,
            )
        }
        HirExprKind::RecordLit { fields, .. } => {
            let mut summary = HirUniqueFlowSummary::default();
            for (_, field_expr) in fields {
                let field_summary = analyze_hir_unique_flow_expr_scoped(
                    field_expr,
                    aliases,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    local_bindings,
                );
                add_ref_counts(&mut summary.ref_counts, &field_summary.ref_counts);
                add_ref_counts(
                    &mut summary.call_escape_counts,
                    &field_summary.call_escape_counts,
                );
            }
            summary
        }
        HirExprKind::RecordUpdate { base, fields, .. } => {
            let mut summary = analyze_hir_unique_flow_expr_scoped(
                base,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            for (_, field_expr) in fields {
                let field_summary = analyze_hir_unique_flow_expr_scoped(
                    field_expr,
                    aliases,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    local_bindings,
                );
                add_ref_counts(&mut summary.ref_counts, &field_summary.ref_counts);
                add_ref_counts(
                    &mut summary.call_escape_counts,
                    &field_summary.call_escape_counts,
                );
            }
            summary.result_alias_root = None;
            summary
        }
        HirExprKind::FieldAccess { expr, .. } => {
            let mut summary = analyze_hir_unique_flow_expr_scoped(
                expr,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            summary.result_alias_root = None;
            summary
        }
        HirExprKind::SumConstructor { fields, .. } => {
            let mut summary = HirUniqueFlowSummary::default();
            for field_expr in fields {
                let field_summary = analyze_hir_unique_flow_expr_scoped(
                    field_expr,
                    aliases,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    local_bindings,
                );
                add_ref_counts(&mut summary.ref_counts, &field_summary.ref_counts);
                add_ref_counts(
                    &mut summary.call_escape_counts,
                    &field_summary.call_escape_counts,
                );
            }
            summary
        }
        HirExprKind::SumPayloadAccess { expr, .. } => {
            let mut summary = analyze_hir_unique_flow_expr_scoped(
                expr,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            summary.result_alias_root = None;
            summary
        }
        HirExprKind::Catch { expr } => analyze_hir_unique_flow_expr_scoped(
            expr,
            aliases,
            safe_handoff_callees,
            safe_higher_order_handoff_callees,
            local_bindings,
        ),
        HirExprKind::Handle {
            expr,
            clauses,
            then_clause,
        } => {
            let mut summary = analyze_hir_unique_flow_expr_scoped(
                expr,
                aliases,
                safe_handoff_callees,
                safe_higher_order_handoff_callees,
                local_bindings,
            );
            let mut clause_count_max = BTreeMap::new();
            let mut clause_escapes_max = BTreeMap::new();
            for clause in clauses {
                let mut clause_bindings = local_bindings.clone();
                for arg in &clause.args {
                    extend_hir_pattern_bindings(arg, &mut clause_bindings);
                }
                let clause_summary = analyze_hir_unique_flow_expr_scoped(
                    &clause.body,
                    aliases,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    &clause_bindings,
                );
                clause_count_max = max_ref_counts(&clause_count_max, &clause_summary.ref_counts);
                clause_escapes_max =
                    max_ref_counts(&clause_escapes_max, &clause_summary.call_escape_counts);
            }
            add_ref_counts(&mut summary.ref_counts, &clause_count_max);
            add_ref_counts(&mut summary.call_escape_counts, &clause_escapes_max);
            if let Some(then_expr) = then_clause {
                let then_summary = analyze_hir_unique_flow_expr_scoped(
                    then_expr,
                    aliases,
                    safe_handoff_callees,
                    safe_higher_order_handoff_callees,
                    local_bindings,
                );
                add_ref_counts(&mut summary.ref_counts, &then_summary.ref_counts);
                add_ref_counts(
                    &mut summary.call_escape_counts,
                    &then_summary.call_escape_counts,
                );
            }
            summary.result_alias_root = None;
            summary
        }
        HirExprKind::Resume { value } => analyze_hir_unique_flow_expr_scoped(
            value,
            aliases,
            safe_handoff_callees,
            safe_higher_order_handoff_callees,
            local_bindings,
        ),
        HirExprKind::Raw(_) => HirUniqueFlowSummary::default(),
    }
}

fn merge_value_roots(
    value_roots: &mut BTreeMap<kea_mir::MirValueId, BTreeSet<String>>,
    dest: &kea_mir::MirValueId,
    roots: &BTreeSet<String>,
) -> bool {
    if roots.is_empty() {
        return false;
    }
    let entry = value_roots.entry(dest.clone()).or_default();
    let before = entry.len();
    entry.extend(roots.iter().cloned());
    entry.len() != before
}

fn collect_mir_unique_flow_summary(
    function: &kea_mir::MirFunction,
    hir_function: &HirFunction,
    unique_param_names: &BTreeSet<String>,
) -> MirUniqueFlowSummary {
    let mut summary = MirUniqueFlowSummary::default();

    let Some(entry_block) = function
        .blocks
        .iter()
        .find(|block| block.id == function.entry)
    else {
        return summary;
    };

    let mut value_roots: BTreeMap<kea_mir::MirValueId, BTreeSet<String>> = BTreeMap::new();
    let Type::Function(hir_fn_ty) = &hir_function.ty else {
        return summary;
    };

    let mut mir_cursor = 0usize;
    for (index, param) in hir_function.params.iter().enumerate() {
        let Some(name) = &param.name else {
            continue;
        };
        if !unique_param_names.contains(name) {
            continue;
        }
        let Some(hir_param_ty) = hir_fn_ty.params.get(index) else {
            continue;
        };
        let mut matched_mir_index = None;
        for mir_index in mir_cursor..function.signature.params.len() {
            if function.signature.params[mir_index] == *hir_param_ty {
                matched_mir_index = Some(mir_index);
                break;
            }
        }
        let Some(mir_index) = matched_mir_index else {
            continue;
        };
        mir_cursor = mir_index.saturating_add(1);
        let Some(entry_param) = entry_block.params.get(mir_index) else {
            continue;
        };
        value_roots
            .entry(entry_param.id.clone())
            .or_default()
            .insert(name.clone());
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in &function.blocks {
            for inst in &block.instructions {
                let (dest, src) = match inst {
                    kea_mir::MirInst::Move { dest, src }
                    | kea_mir::MirInst::Borrow { dest, src }
                    | kea_mir::MirInst::TryClaim { dest, src } => (dest, src),
                    _ => continue,
                };
                let Some(roots) = value_roots.get(src).cloned() else {
                    continue;
                };
                changed |= merge_value_roots(&mut value_roots, dest, &roots);
            }
            if let kea_mir::MirTerminator::Jump { target, args } = &block.terminator
                && let Some(target_block) = function
                    .blocks
                    .iter()
                    .find(|candidate| candidate.id == *target)
            {
                for (arg, param) in args.iter().zip(target_block.params.iter()) {
                    let Some(roots) = value_roots.get(arg).cloned() else {
                        continue;
                    };
                    changed |= merge_value_roots(&mut value_roots, &param.id, &roots);
                }
            }
        }
    }

    for block in &function.blocks {
        for inst in &block.instructions {
            match inst {
                kea_mir::MirInst::Move { src, .. } => {
                    if let Some(roots) = value_roots.get(src) {
                        for root in roots {
                            *summary
                                .move_boundary_counts
                                .entry(root.clone())
                                .or_default() += 1;
                        }
                    }
                }
                kea_mir::MirInst::Freeze { src, .. } => {
                    if let Some(roots) = value_roots.get(src) {
                        for root in roots {
                            *summary
                                .freeze_boundary_counts
                                .entry(root.clone())
                                .or_default() += 1;
                        }
                    }
                }
                _ => {}
            }
        }
    }

    summary
}

fn collect_fip_offending_sites(function: &kea_mir::MirFunction, limit: usize) -> Vec<String> {
    let mut sites = Vec::new();
    for block in &function.blocks {
        for (inst_idx, inst) in block.instructions.iter().enumerate() {
            let op = match inst {
                kea_mir::MirInst::Retain { .. } => Some("Retain"),
                kea_mir::MirInst::Release { .. } => Some("Release"),
                kea_mir::MirInst::RecordInit { .. } => Some("RecordInit"),
                kea_mir::MirInst::SumInit { .. } => Some("SumInit"),
                kea_mir::MirInst::ClosureInit { captures, .. } if captures.is_empty() => None,
                kea_mir::MirInst::ClosureInit { .. } => Some("ClosureInit"),
                kea_mir::MirInst::CowUpdate { .. } => Some("CowUpdate"),
                kea_mir::MirInst::StateCellNew { .. } => Some("StateCellNew"),
                _ => None,
            };
            if let Some(op) = op {
                sites.push(format!("- b{} i{}: {}", block.id.0, inst_idx, op));
                if sites.len() >= limit {
                    return sites;
                }
            }
        }
    }
    sites
}

fn has_errors(diags: &[Diagnostic]) -> bool {
    diags.iter().any(is_error)
}

/// Emit W1001 if a module has public declarations but no module-level doc block.
///
/// Suppressed by `@nodoc` at the top of the file.
fn warn_missing_module_doc(module: &Module, diagnostics: &mut Vec<Diagnostic>) {
    if module.doc.is_some() {
        return;
    }
    let has_nodoc = module
        .annotations
        .iter()
        .any(|a| a.name.node == "nodoc");
    if has_nodoc {
        return;
    }
    let has_pub = module.declarations.iter().any(|d| match &d.node {
        DeclKind::Function(f) => f.public,
        DeclKind::ExprFn(e) => e.public,
        DeclKind::TypeDef(t) => t.public,
        DeclKind::RecordDef(r) => r.public,
        DeclKind::AliasDecl(a) => a.public,
        DeclKind::OpaqueTypeDef(o) => o.public,
        DeclKind::TraitDef(t) => t.public,
        DeclKind::EffectDecl(e) => e.public,
        _ => false,
    });
    if !has_pub {
        return;
    }
    let span = module.span;
    let loc = SourceLocation {
        file_id: span.file.0,
        start: span.start,
        end: span.start, // point at the top of the file
    };
    diagnostics.push(
        Diagnostic::warning(
            Category::MissingModuleDoc,
            "public module has no module-level doc",
        )
        .at(loc)
        .with_help(
            "add a `doc` block followed by a blank line at the top of the file, before any use statements; or add `@nodoc` to suppress this warning",
        ),
    );
}

fn is_error(diag: &Diagnostic) -> bool {
    matches!(diag.severity, Severity::Error)
}

fn span_to_source_location(span: Span) -> SourceLocation {
    SourceLocation {
        file_id: span.file.0,
        start: span.start,
        end: span.end,
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
