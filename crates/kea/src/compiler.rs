use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use kea_ast::{
    DeclKind, Expr, ExprDecl, ExprKind, FileId, FnDecl, ImportItems, Module, RecordDef, Span,
    TestDecl, TypeAnnotation, TypeDef,
};
use kea_codegen::{
    Backend, BackendConfig, CodegenMode, CraneliftBackend, PassStats, default_abi_manifest,
    execute_hir_main_jit,
};
use kea_diag::{Diagnostic, Severity, SourceLocation};
use kea_hir::{
    check_unique_moves_with_borrow_map, collect_borrow_param_positions,
    infer_auto_borrow_param_positions, lower_module, HirModule,
};
use kea_infer::typeck::{
    RecordRegistry, SumTypeRegistry, TraitRegistry, TypeEnv, apply_where_clause,
    concrete_method_types_from_decls,
    infer_and_resolve_in_context, infer_fn_decl_effect_row, register_builtin_int_bitwise_methods,
    register_effect_decl, register_fn_effect_signature, register_fn_signature, resolve_annotation,
    check_expr_in_context,
    seed_fn_where_type_params_in_context, validate_declared_fn_effect_row_with_env_and_records,
    validate_module_annotations, validate_module_fn_annotations, validate_where_clause_traits,
};
use kea_infer::{Category, InferenceContext, Reason};
use kea_mir::lower_hir_module;
use kea_syntax::{lex_layout, parse_module};
use kea_types::{Type, TypeScheme, sanitize_type_display};

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

pub fn compile_module(source: &str, file_id: FileId) -> Result<CompilationContext, String> {
    let (tokens, mut diagnostics) =
        lex_layout(source, file_id).map_err(|diags| format_diagnostics("lexing failed", &diags))?;

    let parsed_module = parse_module(tokens, file_id)
        .map_err(|diags| format_diagnostics("parsing failed", &diags))?;
    let module = expand_impl_methods_for_codegen(&parsed_module);

    let mut env = TypeEnv::new();
    register_builtin_int_bitwise_methods(&mut env);
    let mut records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let mut sum_types = SumTypeRegistry::new();

    diagnostics.extend(validate_module_fn_annotations(&parsed_module));
    diagnostics.extend(validate_module_annotations(&parsed_module));
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
        None,
    )?;

    typecheck_functions(
        &module,
        &mut env,
        &mut records,
        &mut traits,
        &mut sum_types,
        &mut diagnostics,
        None,
    )?;

    let hir = lower_module(&module, &env);
    let explicit_borrow_param_map = collect_borrow_param_positions(&module, None);
    let borrow_param_map = infer_auto_borrow_param_positions(&hir, &explicit_borrow_param_map);
    diagnostics.extend(check_unique_moves_with_borrow_map(&hir, &borrow_param_map));
    if has_errors(&diagnostics) {
        return Err(format_diagnostics("move checking failed", &diagnostics));
    }

    Ok(CompilationContext {
        module,
        hir,
        type_env: env,
        diagnostics,
    })
}

pub fn compile_project(entry: &Path) -> Result<CompilationContext, String> {
    parse_and_typecheck_project(entry)
}

pub fn emit_object(ctx: &CompilationContext, mode: CodegenMode) -> Result<CompileResult, String> {
    let mir = lower_hir_module(&ctx.hir);
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
        stats: artifact.stats,
        diagnostics: ctx.diagnostics.clone(),
    })
}

pub fn execute_jit(ctx: &CompilationContext) -> Result<RunResult, String> {
    let exit_code = execute_hir_main_jit(&ctx.hir, &BackendConfig::default())
        .map_err(|err| format!("codegen failed: {err}"))?;

    Ok(RunResult {
        exit_code,
        diagnostics: ctx.diagnostics.clone(),
    })
}

pub fn compile_file(input: &Path, mode: CodegenMode) -> Result<CompileResult, String> {
    let ctx = compile_project(input)?;
    emit_object(&ctx, mode)
}

pub fn run_file(input: &Path) -> Result<RunResult, String> {
    let ctx = compile_project(input)?;
    execute_jit(&ctx)
}

pub fn run_test_file(input: &Path) -> Result<TestRunResult, String> {
    let loaded_modules = collect_project_modules(input)?;
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
        let main_decl = build_test_main_decl(&test.function_name, scenario_entry.module.span.file)?;
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
        result
            .diagnostics
            .extend(compiled_ctx.diagnostics.clone());

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
    diagnostics.extend(validate_module_fn_annotations(module));
    diagnostics.extend(validate_module_annotations(module));
    if has_errors(&diagnostics) {
        return Err(diagnostics);
    }

    if register_top_level_declarations(
        module,
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

    if typecheck_functions(
        module,
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

    let hir = lower_module(module, env);
    let explicit_borrow_param_map = collect_borrow_param_positions(module, None);
    let borrow_param_map = infer_auto_borrow_param_positions(&hir, &explicit_borrow_param_map);
    diagnostics.extend(check_unique_moves_with_borrow_map(&hir, &borrow_param_map));
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
}

#[derive(Debug)]
struct ModuleResolver {
    stdlib_roots: Vec<PathBuf>,
    source_roots: Vec<PathBuf>,
}

impl ModuleResolver {
    fn for_entry(entry: &Path) -> Self {
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

        fn dedup_existing(paths: Vec<PathBuf>) -> Vec<PathBuf> {
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

        Self {
            stdlib_roots: dedup_existing(stdlib_roots),
            source_roots: dedup_existing(source_roots),
        }
    }

    fn resolve(&self, module_path: &str) -> Option<PathBuf> {
        let rel = module_path
            .split('.')
            .filter(|segment| !segment.is_empty())
            .map(|segment| segment.to_ascii_lowercase())
            .collect::<Vec<_>>();
        if rel.is_empty() {
            return None;
        }

        let mut rel_path = PathBuf::new();
        for segment in rel {
            rel_path.push(segment);
        }
        rel_path.set_extension("kea");

        for root in &self.source_roots {
            let candidate = root.join(&rel_path);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
        for root in &self.stdlib_roots {
            let candidate = root.join(&rel_path);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
        None
    }
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
            if let Some(effect_signature) = env
                .resolve_qualified_effect_signature(&module_path, &item_name)
                .cloned()
            {
                env.set_function_effect_signature(item_name.clone(), effect_signature);
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
        return_annotation: Some(kea_ast::Spanned::new(
            TypeAnnotation::Named("Unit".to_string()),
            test_decl.span,
        )),
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

fn build_test_main_decl(test_fn_name: &str, file_id: FileId) -> Result<kea_ast::Decl, String> {
    let source = format!("fn main() -> Int\n  {test_fn_name}()\n  0\n");
    let (tokens, _) = lex_layout(&source, file_id)
        .map_err(|diags| format_diagnostics("lexing failed", &diags))?;
    let module = parse_module(tokens, file_id)
        .map_err(|diags| format_diagnostics("parsing failed", &diags))?;
    module
        .declarations
        .into_iter()
        .next()
        .ok_or_else(|| "failed to build synthetic test main declaration".to_string())
}

fn collect_project_modules(entry: &Path) -> Result<Vec<LoadedModule>, String> {
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
                let dep_path = resolver.resolve(&dep_module).ok_or_else(|| {
                    format!(
                        "module `{dep_module}` not found while resolving imports for `{module_path}`"
                    )
                })?;
                self.visit(&dep_module, &dep_path, resolver)?;
            }
            self.visiting.pop();

            self.visited.insert(module_path.to_string());
            self.order.push(module_path.to_string());
            self.loaded.insert(
                module_path.to_string(),
                LoadedModule {
                    module_path: module_path.to_string(),
                    module,
                },
            );
            Ok(())
        }
    }

    let entry_path = fs::canonicalize(entry)
        .map_err(|err| format!("failed to read `{}`: {err}", entry.display()))?;
    let resolver = ModuleResolver::for_entry(&entry_path);
    let entry_module_path = module_path_from_entry(&entry_path);
    let mut state = VisitState {
        next_file_id: 0,
        visiting: Vec::new(),
        visited: HashSet::new(),
        loaded: HashMap::new(),
        order: Vec::new(),
    };

    for prelude in configured_prelude_modules() {
        if let Some(prelude_path) = resolver.resolve(&prelude) {
            state.visit(&prelude, &prelude_path, &resolver)?;
        }
    }

    state.visit(&entry_module_path, &entry_path, &resolver)?;

    Ok(state
        .order
        .into_iter()
        .filter_map(|module_path| state.loaded.get(&module_path).cloned())
        .collect())
}

fn merge_modules_for_codegen(modules: &[(String, Module)]) -> Module {
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

    let mut declarations = Vec::new();
    let mut function_decl_indices: BTreeMap<String, usize> = BTreeMap::new();

    for (module_path, module) in modules {
        for decl in &module.declarations {
            match &decl.node {
                DeclKind::Function(fn_decl) => {
                    upsert_function_decl(
                        fn_decl.name.node.clone(),
                        decl.clone(),
                        &mut declarations,
                        &mut function_decl_indices,
                    );

                    if fn_decl.name.node.contains('.') {
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
                    upsert_function_decl(
                        expr_decl.name.node.clone(),
                        decl.clone(),
                        &mut declarations,
                        &mut function_decl_indices,
                    );

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
    let mut records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let mut sum_types = SumTypeRegistry::new();
    let mut diagnostics = Vec::new();
    let mut typed_modules = Vec::new();
    let mut qualified_borrow_param_map = BTreeMap::new();
    for loaded in loaded_modules {
        let expanded = expand_impl_methods_for_codegen(&loaded.module);
        for (name, positions) in
            collect_borrow_param_positions(&expanded, Some(&loaded.module_path))
        {
            if name.contains('.') {
                qualified_borrow_param_map.insert(name, positions);
            }
        }
    }

    for loaded in loaded_modules {
        let is_entry_module = loaded.module_path == entry_module_path;
        let is_prelude_module = prelude_modules.contains(&loaded.module_path);
        let alias_snapshot = (!is_entry_module).then(|| env.snapshot_module_aliases());
        let trait_scope_snapshot = (!is_entry_module).then(|| env.snapshot_in_scope_traits());
        if !is_entry_module {
            env.push_scope();
        }

        let expanded = expand_impl_methods_for_codegen(&loaded.module);

        diagnostics.extend(validate_module_fn_annotations(&loaded.module));
        diagnostics.extend(validate_module_annotations(&loaded.module));
        if has_errors(&diagnostics) {
            if !is_entry_module {
                env.pop_scope();
            }
            return Err(format_diagnostics(
                "type annotation validation failed",
                &diagnostics,
            ));
        }

        register_top_level_declarations(
            &expanded,
            &mut env,
            &mut records,
            &mut traits,
            &mut sum_types,
            &mut diagnostics,
            Some(&loaded.module_path),
        )?;

        let imported_symbols =
            apply_module_imports(&expanded, &mut env, &traits, &mut diagnostics)?;

        // String interpolation desugars to `show(...)` calls in the parser.
        // Re-export hardcoded prelude symbols before typechecking module bodies
        // so those calls resolve in user modules without explicit imports.
        apply_hardcoded_prelude_reexports(&mut env, &traits);

        typecheck_functions(
            &expanded,
            &mut env,
            &mut records,
            &mut traits,
            &mut sum_types,
            &mut diagnostics,
            Some(&loaded.module_path),
        )?;

        let hir = lower_module(&expanded, &env);
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

    let module = merge_modules_for_codegen(&typed_modules);
    let hir = lower_module(&module, &env);
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
    env: &mut TypeEnv,
    diagnostics: &mut Vec<Diagnostic>,
    imported_symbols: &mut Vec<String>,
) {
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

    env.bind(item_name.to_string(), scheme);
    imported_symbols.push(item_name.to_string());

    if let Some(signature) = env
        .resolve_qualified_function_signature(module_path, item_name)
        .cloned()
    {
        env.set_function_signature(item_name.to_string(), signature);
    }
    if let Some(effect_signature) = env
        .resolve_qualified_effect_signature(module_path, item_name)
        .cloned()
    {
        env.set_function_effect_signature(item_name.to_string(), effect_signature);
    }
    if let Some(effect_row) = env.resolve_qualified_effect_row(module_path, item_name) {
        env.set_function_effect_row(item_name.to_string(), effect_row);
    }
}

fn apply_module_imports(
    module: &Module,
    env: &mut TypeEnv,
    traits: &TraitRegistry,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<Vec<String>, String> {
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
                env.mark_trait_in_scope(&item_name);
                imported_symbols.push(item_name);
                continue;
            }
            bind_imported_item(
                &module_path,
                &item_name,
                item.span,
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

fn expand_impl_methods_for_codegen(module: &Module) -> Module {
    let mut declarations = module.declarations.clone();
    let mut trait_method_counts: BTreeMap<(String, String), usize> = BTreeMap::new();
    let mut bare_trait_method_counts: BTreeMap<String, usize> = BTreeMap::new();
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
            // When a trait method has one impl in-module, lift it under
            // `Trait.method` so trait-qualified calls compile on the current
            // monomorphic backend path. Multiple impls get disambiguated names.
            let runtime_name = if duplicate_count == 1 {
                format!("{trait_name}.{method_name}")
            } else {
                format!("{trait_name}.{type_name}.{method_name}")
            };
            lifted.name.node = runtime_name;
            declarations.push(kea_ast::Spanned::new(
                DeclKind::Function(lifted),
                method.span,
            ));

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
                bare.name.node = method_name;
                declarations.push(kea_ast::Spanned::new(DeclKind::Function(bare), method.span));
            }
        }
    }

    Module {
        doc: module.doc.clone(),
        declarations,
        span: module.span,
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
        return Err(format_diagnostics("record registration failed", diagnostics));
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
        return Err(format_diagnostics("record registration failed", diagnostics));
    }

    if let Err(diag) = sum_types.resolve_registered_variants(&type_defs, records) {
        diagnostics.push(diag);
        return Err(format_diagnostics(
            "sum type registration failed",
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
                            if let Some(effect_signature) = env
                                .resolve_qualified_effect_signature(&effect_module, &op_name)
                                .cloned()
                            {
                                env.set_function_effect_signature(
                                    qualified_name.clone(),
                                    effect_signature,
                                );
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

    register_record_const_fields(module, env, records, traits, sum_types, diagnostics, module_path)?;

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
        | ExprKind::Use(_)
        | ExprKind::With { .. }
        | ExprKind::Handle { .. }
        | ExprKind::Resume { .. }
        | ExprKind::WhenGuard { .. }
        | ExprKind::Await { .. }
        | ExprKind::Spawn { .. }
        | ExprKind::StreamBlock { .. }
        | ExprKind::Yield { .. }
        | ExprKind::YieldFrom { .. }
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
            const_expr_supported(base) && fields.iter().all(|(_, value)| const_expr_supported(value))
        }
        ExprKind::Constructor { args, .. } => args.iter().all(|arg| const_expr_supported(&arg.value)),
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
        | ExprKind::Use(_)
        | ExprKind::With { .. }
        | ExprKind::Handle { .. }
        | ExprKind::Resume { .. }
        | ExprKind::WhenGuard { .. }
        | ExprKind::Await { .. }
        | ExprKind::Spawn { .. }
        | ExprKind::StreamBlock { .. }
        | ExprKind::Yield { .. }
        | ExprKind::YieldFrom { .. }
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
            let start = stack
                .iter()
                .position(|item| item == name)
                .unwrap_or(0);
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
            let Some(resolved) = resolve_annotation(&const_field.annotation, records, Some(sum_types))
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

fn typecheck_functions(
    module: &Module,
    env: &mut TypeEnv,
    records: &mut RecordRegistry,
    traits: &mut TraitRegistry,
    sum_types: &mut SumTypeRegistry,
    diagnostics: &mut Vec<Diagnostic>,
    module_path: Option<&str>,
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

        if let Some(module_path) = module_path {
            let module_short = module_struct_name(module_path).to_string();
            if env.resolve_module_path_alias(&module_short).is_none() {
                env.register_module_alias(&module_short, module_path);
            }
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
            if let Some(effect_sig) = env.function_effect_signature(&fn_decl.name.node).cloned() {
                env.set_function_effect_signature(qualified_name.clone(), effect_sig);
            }
            if let Some(effect_row) = env.function_effect_row(&fn_decl.name.node) {
                env.set_function_effect_row(qualified_name, effect_row);
            }
        }
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
