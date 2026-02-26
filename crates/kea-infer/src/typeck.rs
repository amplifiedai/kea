//! Expression-level type inference with let-generalization.
//!
//! This module walks AST expressions and infers their types using the
//! Unifier for eager unification. Key features:
//!
//! - Let-generalization: polymorphic `let` bindings get type schemes
//! - Instantiation: each use of a polymorphic binding gets fresh variables
//! - Lacks constraints survive generalization and transfer on instantiation
//!
//! The type checker operates on hand-built or parsed ASTs and produces
//! types with all inference variables resolved via substitution.

use std::collections::{BTreeMap, BTreeSet};

use kea_ast::{
    AliasDecl, Argument, BinOp, EffectDecl, Expr, ExprKind, FnDecl, ForClause, ForExpr, Lit,
    OpaqueTypeDef, Param, ParamLabel, Pattern, PatternKind, RecordDef, Span, TypeAnnotation,
    free_vars,
};
use kea_types::{
    Dim, DimVarId, EffectRow, Effects, FunctionType, Kind, Label, Purity, RecordType, RowType,
    RowVarId, Substitution, SumType, Type, TypeScheme, TypeVarId, Volatility,
    builtin_type_constructor_arity, free_dim_vars, free_row_vars, free_type_vars, is_sendable,
    rebuild_type, sendable_violation, type_constructor_for_trait,
};

use crate::{
    Category, Constraint, Diagnostic, InferenceContext, Provenance, Reason, SourceLocation,
    Unifier,
};

/// Runtime type annotations emitted during expression inference.
///
/// These annotations are consumed by the evaluator to resolve trait
/// dictionaries ("evidence") at runtime call sites.
#[derive(Debug, Clone, Default)]
pub struct TypeAnnotations {
    /// Trait evidence requirements at call-like expression spans.
    pub evidence_sites: BTreeMap<Span, Vec<EvidenceSite>>,
    /// Existential argument pack plans at call-like expression spans.
    /// The evaluator uses this to wrap concrete values into
    /// `Value::Existential` with pre-resolved dictionaries.
    pub existential_packs: BTreeMap<Span, Vec<ExistentialPackSite>>,
    /// Type-directed lowering for `for` expressions at expression span.
    pub for_desugared: BTreeMap<Span, Expr>,
    /// Type-directed lowering for `use` chain heads at expression span.
    pub use_desugared: BTreeMap<Span, Expr>,
    /// Type-directed spawn dispatch at expression span.
    pub spawn_kinds: BTreeMap<Span, SpawnKind>,
    /// Resolved variant type names for ambiguous constructors.
    /// Maps the span of the constructor use to the owning sum type name.
    /// The evaluator uses this to know which type to construct when variant
    /// names are shared across multiple sum types.
    pub resolved_variants: BTreeMap<Span, String>,
    /// Resolved target type names for `expect_type` calls.
    /// Maps the span of the `expect_type(...)` call to the resolved type name.
    /// The evaluator uses this to perform runtime type checking.
    pub expect_type_targets: BTreeMap<Span, String>,
}

/// Runtime dispatch mode for `spawn` expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpawnKind {
    Actor,
    Task,
}

/// A single trait evidence requirement at a call site.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct EvidenceSite {
    pub trait_name: String,
    pub type_name: String,
    pub associated_types: BTreeMap<String, String>,
}

/// Runtime pack information for a single existential argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExistentialPackSite {
    pub arg_index: usize,
    pub concrete_type: Type,
    pub bounds: Vec<String>,
    pub associated_types: BTreeMap<String, Type>,
}

/// Effect-signature template for a function used during effect inference.
///
/// This captures declared effect variables in parameter function types and the
/// function's own declared effect term. Templates are instantiated with fresh
/// effect variables at each call site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionEffectSignature {
    pub param_effect_rows: Vec<Option<EffectRow>>,
    pub effect_row: EffectRow,
    /// Whether this signature is a polymorphic template that should be
    /// instantiated with fresh effect vars at each call site.
    ///
    /// Local callback parameters use `false` so their effect variables stay
    /// linked within the current inference scope.
    pub instantiate_on_call: bool,
}

/// Call-site signature metadata for named/labeled argument binding.
///
/// Labels/defaults are call-resolution metadata only; they are erased from
/// `Type::Function` equality/unification.
#[derive(Debug, Clone, PartialEq)]
pub struct FnSignature {
    pub params: Vec<FnParamSignature>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnParamSignature {
    /// Bound parameter name (used for default-expression scope), when simple.
    pub name: Option<String>,
    /// Call-site label. `None` means positional-only (`_` parameter).
    pub label: Option<String>,
    /// Default expression evaluated at call site when omitted.
    pub default: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ResumeContext {
    operation_return: Type,
    clause_result: Type,
}

impl FnSignature {
    /// Build an all-positional signature with no defaults.
    pub fn all_positional(arity: usize) -> Self {
        Self {
            params: (0..arity)
                .map(|_| FnParamSignature {
                    name: None,
                    label: None,
                    default: None,
                })
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BoundArg {
    Provided(Expr),
    Default(Expr),
}

fn bound_arg_expr(bound_arg: &BoundArg) -> &Expr {
    match bound_arg {
        BoundArg::Provided(expr) | BoundArg::Default(expr) => expr,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgBindErrorKind {
    UnknownLabel { label: String },
    DuplicateLabel { label: String },
    MissingRequired { index: usize, label: Option<String> },
    TooManyArguments { expected: usize, got: usize },
    PositionalAfterLabeled,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgBindError {
    pub kind: ArgBindErrorKind,
    pub span: Option<Span>,
}

/// Resolve call arguments against a function signature.
///
/// Returns argument expressions in declaration order, with defaults inserted.
pub fn bind_args(
    signature: &FnSignature,
    args: &[Argument],
) -> Result<Vec<BoundArg>, ArgBindError> {
    let mut assigned: Vec<Option<BoundArg>> = vec![None; signature.params.len()];
    let mut seen_labeled = false;
    let mut next_positional = 0usize;

    let label_to_index: BTreeMap<&str, usize> = signature
        .params
        .iter()
        .enumerate()
        .filter_map(|(idx, p)| p.label.as_deref().map(|label| (label, idx)))
        .collect();

    for arg in args {
        if let Some(label) = &arg.label {
            seen_labeled = true;
            let label_name = label.node.as_str();
            let Some(index) = label_to_index.get(label_name).copied() else {
                return Err(ArgBindError {
                    kind: ArgBindErrorKind::UnknownLabel {
                        label: label.node.clone(),
                    },
                    span: Some(label.span),
                });
            };
            if assigned[index].is_some() {
                return Err(ArgBindError {
                    kind: ArgBindErrorKind::DuplicateLabel {
                        label: label.node.clone(),
                    },
                    span: Some(label.span),
                });
            }
            assigned[index] = Some(BoundArg::Provided(arg.value.clone()));
            continue;
        }

        if seen_labeled {
            return Err(ArgBindError {
                kind: ArgBindErrorKind::PositionalAfterLabeled,
                span: Some(arg.value.span),
            });
        }

        while next_positional < assigned.len() && assigned[next_positional].is_some() {
            next_positional += 1;
        }
        if next_positional >= assigned.len() {
            return Err(ArgBindError {
                kind: ArgBindErrorKind::TooManyArguments {
                    expected: signature.params.len(),
                    got: args.len(),
                },
                span: Some(arg.value.span),
            });
        }
        assigned[next_positional] = Some(BoundArg::Provided(arg.value.clone()));
        next_positional += 1;
    }

    for (idx, slot) in assigned.iter_mut().enumerate() {
        if slot.is_some() {
            continue;
        }
        if let Some(default) = &signature.params[idx].default {
            *slot = Some(BoundArg::Default(default.clone()));
            continue;
        }
        return Err(ArgBindError {
            kind: ArgBindErrorKind::MissingRequired {
                index: idx,
                label: signature.params[idx].label.clone(),
            },
            span: None,
        });
    }

    Ok(assigned
        .into_iter()
        .map(|arg| arg.expect("all arguments should be assigned"))
        .collect())
}

// ---------------------------------------------------------------------------
// Type environment
// ---------------------------------------------------------------------------

/// Maps variable names to their type schemes.
///
/// Uses a stack of scopes for lexical scoping: inner scopes shadow outer ones.
#[derive(Debug, Clone)]
pub struct TypeEnv {
    bindings: Vec<BTreeMap<String, TypeScheme>>,
    function_effects: BTreeMap<String, Effects>,
    function_effect_rows: BTreeMap<String, EffectRow>,
    function_effect_signatures: BTreeMap<String, FunctionEffectSignature>,
    function_signatures: BTreeMap<String, FnSignature>,
    module_functions: BTreeMap<String, Vec<String>>,
    /// Module-scoped type schemes: full module path → (fn name → (scheme, effects)).
    /// Enables qualified access (`Math.sqrt`) without requiring bare name binding.
    module_type_schemes: BTreeMap<String, BTreeMap<String, (TypeScheme, Effects)>>,
    /// Short module name → full module path (e.g. "Math" → "Kea.Math").
    /// Populated during import resolution and session init.
    module_aliases: BTreeMap<String, String>,
    /// Stack of enclosing stream element types for `stream { ... }` blocks.
    stream_contexts: Vec<Type>,
    /// Nesting depth for actor-method inference contexts.
    ///
    /// Used for warnings about operations that can block an actor mailbox
    /// (for example `await` inside an actor impl method body).
    actor_context_depth: usize,
    /// Active resume contexts for nested handler clauses.
    resume_contexts: Vec<ResumeContext>,
}

impl TypeEnv {
    fn apply_effect_row_to_scheme(scheme: &mut TypeScheme, row: &EffectRow) {
        if let Type::Function(ft) = &mut scheme.ty {
            ft.effects = row.clone();
        }
    }

    fn update_bound_function_effect(&mut self, name: &str, row: &EffectRow) {
        for scope in self.bindings.iter_mut().rev() {
            if let Some(scheme) = scope.get_mut(name) {
                Self::apply_effect_row_to_scheme(scheme, row);
                break;
            }
        }
    }

    fn update_module_function_effect(&mut self, name: &str, row: &EffectRow) {
        if let Some((module_path, fn_name)) = name.split_once("::")
            && let Some(module) = self.module_type_schemes.get_mut(module_path)
            && let Some((scheme, effects)) = module.get_mut(fn_name)
        {
            Self::apply_effect_row_to_scheme(scheme, row);
            *effects = classify_effect_row(row);
            return;
        }

        for module in self.module_type_schemes.values_mut() {
            if let Some((scheme, effects)) = module.get_mut(name) {
                Self::apply_effect_row_to_scheme(scheme, row);
                *effects = classify_effect_row(row);
            }
        }
    }

    fn effect_row_from_type(ty: &Type) -> Option<EffectRow> {
        match ty {
            Type::Function(ft) => Some(ft.effects.clone()),
            Type::Forall(inner) => Self::effect_row_from_type(&inner.ty),
            _ => None,
        }
    }

    fn effect_row_from_scheme(scheme: &TypeScheme) -> Option<EffectRow> {
        Self::effect_row_from_type(&scheme.ty)
    }

    fn ensure_module_alias_for_path(&mut self, module_path: &str) {
        let Some((_prefix, short)) = module_path.rsplit_once('.') else {
            return;
        };
        self.module_aliases
            .entry(short.to_string())
            .or_insert_with(|| module_path.to_string());
    }

    pub fn new() -> Self {
        Self {
            bindings: vec![BTreeMap::new()],
            function_effects: BTreeMap::new(),
            function_effect_rows: BTreeMap::new(),
            function_effect_signatures: BTreeMap::new(),
            function_signatures: BTreeMap::new(),
            module_functions: BTreeMap::new(),
            module_type_schemes: BTreeMap::new(),
            module_aliases: BTreeMap::new(),
            stream_contexts: Vec::new(),
            actor_context_depth: 0,
            resume_contexts: Vec::new(),
        }
    }

    /// Record the inferred/declared effects for a function binding.
    pub fn set_function_effect(&mut self, name: String, effects: Effects) {
        let row = effect_row_from_effects(effects);
        self.function_effect_rows.insert(name.clone(), row.clone());
        self.function_effects.insert(name.clone(), effects);
        self.update_bound_function_effect(&name, &row);
        self.update_module_function_effect(&name, &row);
    }

    /// Record an effect row for a function binding (for effect-polymorphic callbacks).
    pub fn set_function_effect_row(&mut self, name: String, row: EffectRow) {
        self.function_effects
            .insert(name.clone(), classify_effect_row(&row));
        self.function_effect_rows.insert(name.clone(), row.clone());
        self.update_bound_function_effect(&name, &row);
        self.update_module_function_effect(&name, &row);
    }

    /// Register a function effect-signature template for call-site instantiation.
    pub fn set_function_effect_signature(
        &mut self,
        name: String,
        signature: FunctionEffectSignature,
    ) {
        self.function_effect_signatures.insert(name, signature);
    }

    /// Register call-site signature metadata for a function binding.
    pub fn set_function_signature(&mut self, name: String, signature: FnSignature) {
        self.function_signatures.insert(name, signature);
    }

    /// Get effects for a function binding, if known.
    pub fn function_effect(&self, name: &str) -> Option<Effects> {
        self.function_effects.get(name).copied()
    }

    /// Get effect row for a function binding, if known.
    pub fn function_effect_row(&self, name: &str) -> Option<EffectRow> {
        if let Some(row) = self.function_effect_rows.get(name) {
            return Some(row.clone());
        }
        for scope in self.bindings.iter().rev() {
            if let Some(scheme) = scope.get(name)
                && let Some(row) = Self::effect_row_from_scheme(scheme)
            {
                return Some(row);
            }
        }
        None
    }

    /// Get effect-signature template for a function binding, if present.
    pub fn function_effect_signature(&self, name: &str) -> Option<&FunctionEffectSignature> {
        self.function_effect_signatures.get(name)
    }

    /// Get call-site signature metadata for a function binding.
    pub fn function_signature(&self, name: &str) -> Option<&FnSignature> {
        self.function_signatures.get(name)
    }

    /// Register a function as a member of a module path (`Kea.List`, etc.).
    pub fn register_module_function(&mut self, module: &str, name: &str) {
        self.module_functions
            .entry(module.to_string())
            .or_default()
            .push(name.to_string());
        self.ensure_module_alias_for_path(module);
    }

    /// Register a type scheme in the module-scoped map for qualified access.
    pub fn register_module_type_scheme(
        &mut self,
        module_path: &str,
        name: &str,
        mut scheme: TypeScheme,
        effects: Effects,
    ) {
        let row = effect_row_from_effects(effects);
        Self::apply_effect_row_to_scheme(&mut scheme, &row);
        self.module_type_schemes
            .entry(module_path.to_string())
            .or_default()
            .insert(name.to_string(), (scheme, effects));
        self.ensure_module_alias_for_path(module_path);
    }

    /// Register a short module alias (e.g. "Math" → "Kea.Math").
    pub fn register_module_alias(&mut self, short: &str, full_path: &str) {
        self.module_aliases
            .insert(short.to_string(), full_path.to_string());
    }

    /// Resolve `Module.member` to a bound function scheme when available.
    ///
    /// Checks only module-scoped type schemes; qualified lookup does not
    /// consult flat/global bindings.
    pub fn resolve_qualified(&self, module_short: &str, field: &str) -> Option<&TypeScheme> {
        // Resolve the short name to a full module path.
        let module_path = self
            .module_aliases
            .get(module_short)
            .cloned()
            .unwrap_or_else(|| format!("Kea.{module_short}"));

        // Check module-scoped type schemes first (primary path).
        if let Some(module) = self.module_type_schemes.get(&module_path) {
            if let Some((scheme, _)) = module.get(field) {
                return Some(scheme);
            }
            // Try prefixed form (e.g. "len" → "list_len").
            let prefixed = format!("{}_{}", module_short.to_lowercase(), field);
            if let Some((scheme, _)) = module.get(&prefixed) {
                return Some(scheme);
            }
        }
        None
    }

    /// Resolve effects for a qualified function reference.
    pub fn resolve_qualified_effects(&self, module_short: &str, field: &str) -> Option<Effects> {
        let module_path = self
            .module_aliases
            .get(module_short)
            .cloned()
            .unwrap_or_else(|| format!("Kea.{module_short}"));

        if let Some(module) = self.module_type_schemes.get(&module_path) {
            if let Some((_, effects)) = module.get(field) {
                return Some(*effects);
            }
            let prefixed = format!("{}_{}", module_short.to_lowercase(), field);
            if let Some((_, effects)) = module.get(&prefixed) {
                return Some(*effects);
            }
        }
        None
    }

    /// Resolve effect term for a qualified function reference.
    pub fn resolve_qualified_effect_row(
        &self,
        module_short: &str,
        field: &str,
    ) -> Option<EffectRow> {
        let module_path = self
            .module_aliases
            .get(module_short)
            .cloned()
            .unwrap_or_else(|| format!("Kea.{module_short}"));

        if let Some(module) = self.module_type_schemes.get(&module_path) {
            if let Some((scheme, effects)) = module.get(field) {
                return Self::effect_row_from_scheme(scheme)
                    .or_else(|| Some(effect_row_from_effects(*effects)));
            }
            let prefixed = format!("{}_{}", module_short.to_lowercase(), field);
            if let Some((scheme, effects)) = module.get(&prefixed) {
                return Self::effect_row_from_scheme(scheme)
                    .or_else(|| Some(effect_row_from_effects(*effects)));
            }
        }
        None
    }

    /// Resolve effect-signature template for a qualified function reference.
    pub fn resolve_qualified_effect_signature(
        &self,
        module_short: &str,
        field: &str,
    ) -> Option<&FunctionEffectSignature> {
        let module_path = self
            .module_aliases
            .get(module_short)
            .cloned()
            .unwrap_or_else(|| format!("Kea.{module_short}"));
        if let Some(candidates) = self.module_functions.get(&module_path) {
            // Try module-qualified key first to avoid collision with bare-name globals.
            let qualified_key = format!("{module_path}::{field}");
            if candidates.iter().any(|name| name == field) {
                if let Some(sig) = self.function_effect_signature(&qualified_key) {
                    return Some(sig);
                }
                if let Some(sig) = self.function_effect_signature(field) {
                    return Some(sig);
                }
                let prefixed = format!("{}_{}", module_short.to_lowercase(), field);
                return self.function_effect_signature(&prefixed);
            }
            let prefixed = format!("{}_{}", module_short.to_lowercase(), field);
            if candidates.iter().any(|name| name == &prefixed) {
                let prefixed_qualified = format!("{module_path}::{prefixed}");
                if let Some(sig) = self.function_effect_signature(&prefixed_qualified) {
                    return Some(sig);
                }
                return self.function_effect_signature(&prefixed);
            }
        }
        // Fall through to trait-qualified lookup: `Comprehensible::map`, etc.
        let trait_key = format!("{module_short}::{field}");
        self.function_effect_signature(&trait_key)
    }

    /// Resolve call-signature metadata for a qualified function reference.
    pub fn resolve_qualified_function_signature(
        &self,
        module_short: &str,
        field: &str,
    ) -> Option<&FnSignature> {
        let module_path = self
            .module_aliases
            .get(module_short)
            .cloned()
            .unwrap_or_else(|| format!("Kea.{module_short}"));
        let candidates = self.module_functions.get(&module_path)?;
        // Try module-qualified key first to avoid collision with bare-name globals.
        let qualified_key = format!("{module_path}::{field}");
        if candidates.iter().any(|name| name == field) {
            if let Some(sig) = self.function_signature(&qualified_key) {
                return Some(sig);
            }
            if let Some(sig) = self.function_signature(field) {
                return Some(sig);
            }
            let prefixed = format!("{}_{}", module_short.to_lowercase(), field);
            return self.function_signature(&prefixed);
        }
        let prefixed = format!("{}_{}", module_short.to_lowercase(), field);
        if candidates.iter().any(|name| name == &prefixed) {
            let prefixed_qualified = format!("{module_path}::{prefixed}");
            if let Some(sig) = self.function_signature(&prefixed_qualified) {
                return Some(sig);
            }
            return self.function_signature(&prefixed);
        }
        None
    }

    /// Check whether a short module name is known in the environment.
    ///
    /// Checks alias map first (covers both stdlib like "Math" → "Kea.Math"
    /// and extensions like "Grpc" → "Grpc"), then falls back to "Kea." prefix.
    pub fn has_qualified_module(&self, module_short: &str) -> bool {
        let module_path = self
            .module_aliases
            .get(module_short)
            .cloned()
            .unwrap_or_else(|| format!("Kea.{module_short}"));
        self.module_functions.contains_key(&module_path)
            || self.module_type_schemes.contains_key(&module_path)
    }

    /// Return all function names registered in a module (by full path).
    pub fn module_function_names(&self, module_path: &str) -> Option<Vec<String>> {
        self.module_type_schemes
            .get(module_path)
            .map(|m| m.keys().cloned().collect())
    }

    /// Look up a type scheme registered in a module by full path and name.
    pub fn lookup_module_type_scheme(&self, module_path: &str, name: &str) -> Option<TypeScheme> {
        self.module_type_schemes
            .get(module_path)
            .and_then(|m| m.get(name))
            .map(|(scheme, _)| scheme.clone())
    }

    /// Look up effects for a module-registered function by full path and name.
    pub fn module_function_effect(&self, module_path: &str, name: &str) -> Option<Effects> {
        self.module_type_schemes
            .get(module_path)
            .and_then(|m| m.get(name))
            .map(|(_, effects)| *effects)
    }

    /// Look up a name, searching from innermost to outermost scope.
    pub fn lookup(&self, name: &str) -> Option<&TypeScheme> {
        for scope in self.bindings.iter().rev() {
            if let Some(scheme) = scope.get(name) {
                return Some(scheme);
            }
        }
        None
    }

    /// Bind a name in the current (innermost) scope.
    pub fn bind(&mut self, name: String, scheme: TypeScheme) {
        debug_assert!(
            {
                let free_tvs = free_type_vars(&scheme.ty);
                let free_rvs = free_row_vars(&scheme.ty);
                let free_dvs = free_dim_vars(&scheme.ty);

                // Every quantified variable must appear free in the body type.
                let phantom_tvs: Vec<_> = scheme
                    .type_vars
                    .iter()
                    .filter(|tv| !free_tvs.contains(tv))
                    .collect();
                let phantom_rvs: Vec<_> = scheme
                    .row_vars
                    .iter()
                    .filter(|rv| !free_rvs.contains(rv))
                    .collect();
                let phantom_dvs: Vec<_> = scheme
                    .dim_vars
                    .iter()
                    .filter(|dv| !free_dvs.contains(dv))
                    .collect();

                // Lacks constraints must reference quantified row vars.
                let quantified_rvs: BTreeSet<_> =
                    scheme.row_vars.iter().copied().collect();
                let dangling_lacks: Vec<_> = scheme
                    .lacks
                    .keys()
                    .filter(|rv| !quantified_rvs.contains(rv))
                    .collect();

                // Trait bounds must reference quantified type vars.
                let quantified_tvs: BTreeSet<_> =
                    scheme.type_vars.iter().copied().collect();
                let dangling_bounds: Vec<_> = scheme
                    .bounds
                    .keys()
                    .filter(|tv| !quantified_tvs.contains(tv))
                    .collect();

                // Kind assignments must reference quantified type vars.
                let dangling_kinds: Vec<_> = scheme
                    .kinds
                    .keys()
                    .filter(|tv| !quantified_tvs.contains(tv))
                    .collect();

                if !phantom_tvs.is_empty()
                    || !phantom_rvs.is_empty()
                    || !phantom_dvs.is_empty()
                    || !dangling_lacks.is_empty()
                    || !dangling_bounds.is_empty()
                    || !dangling_kinds.is_empty()
                {
                    eprintln!(
                        "Malformed TypeScheme for '{name}':\n  \
                         ty: {:?}\n  \
                         phantom type_vars: {phantom_tvs:?}\n  \
                         phantom row_vars: {phantom_rvs:?}\n  \
                         phantom dim_vars: {phantom_dvs:?}\n  \
                         dangling lacks: {dangling_lacks:?}\n  \
                         dangling bounds: {dangling_bounds:?}\n  \
                         dangling kinds: {dangling_kinds:?}",
                        scheme.ty
                    );
                    false
                } else {
                    true
                }
            },
            "TypeEnv::bind called with malformed TypeScheme for '{name}'"
        );
        self.bindings.last_mut().unwrap().insert(name, scheme);
    }

    /// Push a new scope (for let bodies, lambda bodies, etc.).
    pub fn push_scope(&mut self) {
        self.bindings.push(BTreeMap::new());
    }

    /// Pop the innermost scope.
    pub fn pop_scope(&mut self) {
        debug_assert!(!self.bindings.is_empty(), "pop_scope called with no scopes");
        self.bindings.pop();
    }

    pub fn push_stream_context(&mut self, elem_ty: Type) {
        self.stream_contexts.push(elem_ty);
    }

    pub fn pop_stream_context(&mut self) {
        debug_assert!(
            !self.stream_contexts.is_empty(),
            "pop_stream_context called with no stream contexts"
        );
        self.stream_contexts.pop();
    }

    pub fn current_stream_context(&self) -> Option<&Type> {
        self.stream_contexts.last()
    }

    /// Enter actor-method inference context.
    pub fn push_actor_context(&mut self) {
        self.actor_context_depth = self.actor_context_depth.saturating_add(1);
    }

    /// Exit actor-method inference context.
    pub fn pop_actor_context(&mut self) {
        self.actor_context_depth = self.actor_context_depth.saturating_sub(1);
    }

    /// True when currently inferring inside an actor method body.
    pub fn in_actor_context(&self) -> bool {
        self.actor_context_depth > 0
    }

    fn push_resume_context(&mut self, operation_return: Type, clause_result: Type) {
        self.resume_contexts.push(ResumeContext {
            operation_return,
            clause_result,
        });
    }

    fn current_resume_context(&self) -> Option<&ResumeContext> {
        self.resume_contexts.last()
    }

    /// Return all visible names with their type representations.
    ///
    /// Inner scopes shadow outer ones, matching `lookup` semantics.
    pub fn all_names_with_types(&self) -> Vec<(String, String)> {
        self.all_names_with_schemes()
            .into_iter()
            .map(|(name, scheme)| (name, scheme.ty.to_string()))
            .collect()
    }

    /// Return all visible names with their full type schemes.
    ///
    /// Inner scopes shadow outer ones. Results are sorted by name.
    /// Use this when you need to inspect the actual `Type` enum
    /// (e.g., for classify_binding or type variable sanitization).
    pub fn all_names_with_schemes(&self) -> Vec<(String, TypeScheme)> {
        let mut seen = std::collections::HashSet::new();
        let mut result = Vec::new();
        for scope in self.bindings.iter().rev() {
            for (name, scheme) in scope {
                if seen.insert(name.clone()) {
                    result.push((name.clone(), scheme.clone()));
                }
            }
        }
        result.sort_by(|a, b| a.0.cmp(&b.0));
        result
    }
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Record registry
// ---------------------------------------------------------------------------

/// Registry of named record definitions.
///
/// Maps record names to their field types. Used by `resolve_annotation` to
/// resolve user-defined type names and by expression inference for record construction.
#[derive(Debug, Clone)]
pub struct RecordRegistry {
    records: BTreeMap<String, RecordInfo>,
    aliases: BTreeMap<String, AliasInfo>,
    opaques: BTreeMap<String, OpaqueTypeInfo>,
}

/// Type-level information about a named record, derived from its definition.
#[derive(Debug, Clone)]
pub struct RecordInfo {
    pub params: Vec<String>,
    pub row: RowType,
    /// Source span of the record name in its definition.
    /// `None` for builtin types without source locations.
    pub definition_span: Option<Span>,
    /// Doc comment from `///` above the record definition.
    pub doc: Option<String>,
    /// Whether this record was declared `pub`.
    pub public: bool,
}

/// Type-level information about a named alias.
#[derive(Debug, Clone)]
pub struct AliasInfo {
    pub params: Vec<String>,
    pub target: TypeAnnotation,
    /// Source span of the alias name in its definition.
    pub definition_span: Option<Span>,
    /// Doc comment from `///` above the alias definition.
    pub doc: Option<String>,
    pub public: bool,
}

/// Type-level information about a named opaque type.
#[derive(Debug, Clone)]
pub struct OpaqueTypeInfo {
    pub params: Vec<String>,
    pub target: TypeAnnotation,
    /// Source span of the opaque type name in its definition.
    pub definition_span: Option<Span>,
    /// Doc comment from `///` above the opaque definition.
    pub doc: Option<String>,
    pub public: bool,
}

impl RecordRegistry {
    pub fn new() -> Self {
        Self {
            records: BTreeMap::new(),
            aliases: BTreeMap::new(),
            opaques: BTreeMap::new(),
        }
    }

    /// Register a type alias definition.
    pub fn register_alias(&mut self, def: &AliasDecl) -> Result<(), Diagnostic> {
        if self.records.contains_key(&def.name.node)
            || self.aliases.contains_key(&def.name.node)
            || self.opaques.contains_key(&def.name.node)
        {
            return Err(Diagnostic::error(
                Category::TypeMismatch,
                format!("type `{}` is already defined", def.name.node),
            )
            .at(SourceLocation {
                file_id: def.name.span.file.0,
                start: def.name.span.start,
                end: def.name.span.end,
            }));
        }

        self.aliases.insert(
            def.name.node.clone(),
            AliasInfo {
                params: def.params.clone(),
                target: def.target.node.clone(),
                definition_span: Some(def.name.span),
                doc: def.doc.clone(),
                public: def.public,
            },
        );

        if self.alias_has_cycle() {
            self.aliases.remove(&def.name.node);
            return Err(Diagnostic::error(
                Category::TypeMismatch,
                format!("cyclic alias definition involving `{}`", def.name.node),
            )
            .at(SourceLocation {
                file_id: def.name.span.file.0,
                start: def.name.span.start,
                end: def.name.span.end,
            }));
        }

        Ok(())
    }

    /// Register an opaque type definition.
    pub fn register_opaque(&mut self, def: &OpaqueTypeDef) -> Result<(), Diagnostic> {
        if self.records.contains_key(&def.name.node)
            || self.aliases.contains_key(&def.name.node)
            || self.opaques.contains_key(&def.name.node)
        {
            return Err(Diagnostic::error(
                Category::TypeMismatch,
                format!("type `{}` is already defined", def.name.node),
            )
            .at(SourceLocation {
                file_id: def.name.span.file.0,
                start: def.name.span.start,
                end: def.name.span.end,
            }));
        }

        self.opaques.insert(
            def.name.node.clone(),
            OpaqueTypeInfo {
                params: def.params.clone(),
                target: def.target.node.clone(),
                definition_span: Some(def.name.span),
                doc: def.doc.clone(),
                public: def.public,
            },
        );

        Ok(())
    }

    /// Register a record definition, converting its AST fields to a RowType.
    ///
    /// Returns an error diagnostic if any field type annotation cannot be resolved.
    pub fn register(&mut self, def: &RecordDef) -> Result<(), Diagnostic> {
        // Check for duplicate field names
        let mut seen: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
        for (name, _) in &def.fields {
            if !seen.insert(&name.node) {
                return Err(Diagnostic::error(
                    Category::TypeMismatch,
                    format!(
                        "duplicate field `{}` in record `{}`",
                        name.node, def.name.node,
                    ),
                )
                .at(SourceLocation {
                    file_id: name.span.file.0,
                    start: name.span.start,
                    end: name.span.end,
                }));
            }
        }

        let type_param_scope: BTreeMap<String, Type> = def
            .params
            .iter()
            .enumerate()
            .map(|(idx, name)| (name.clone(), Type::Var(TypeVarId(idx as u32))))
            .collect();

        let mut fields: Vec<(Label, Type)> = Vec::new();
        for (name, ann) in &def.fields {
            match resolve_annotation_with_type_params(ann, &type_param_scope, self, None) {
                Some(ty) => fields.push((Label::new(name.node.clone()), ty)),
                None => {
                    return Err(Diagnostic::error(
                        Category::TypeMismatch,
                        format!(
                            "unknown type `{}` in field `{}` of record `{}`",
                            annotation_display(ann),
                            name.node,
                            def.name.node,
                        ),
                    )
                    .at(SourceLocation {
                        file_id: name.span.file.0,
                        start: name.span.start,
                        end: name.span.end,
                    }));
                }
            }
        }
        let row = RowType::closed(fields);
        self.records.insert(
            def.name.node.clone(),
            RecordInfo {
                params: def.params.clone(),
                row,
                definition_span: Some(def.name.span),
                doc: def.doc.clone(),
                public: def.public,
            },
        );
        Ok(())
    }

    /// Look up a record by name.
    pub fn lookup(&self, name: &str) -> Option<&RecordInfo> {
        self.records.get(name)
    }

    /// Look up an alias by name.
    pub fn lookup_alias(&self, name: &str) -> Option<&AliasInfo> {
        self.aliases.get(name)
    }

    /// Look up an opaque type by name.
    pub fn lookup_opaque(&self, name: &str) -> Option<&OpaqueTypeInfo> {
        self.opaques.get(name)
    }

    /// Convert a record name to its nominal type.
    pub fn to_type(&self, name: &str) -> Option<Type> {
        self.to_type_with(name, &mut None)
    }

    /// Convert with an optional unifier for fresh type var generation.
    /// If unifier is None, uses placeholder vars for record params.
    pub fn to_type_with(&self, name: &str, unifier: &mut Option<&mut Unifier>) -> Option<Type> {
        let info = self.lookup(name)?;
        if info.params.is_empty() {
            return Some(Type::Record(RecordType {
                name: name.to_string(),
                params: vec![],
                row: info.row.clone(),
            }));
        }

        let replacements: Vec<Type> = info
            .params
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                if let Some(u) = unifier.as_mut() {
                    u.fresh_type()
                } else {
                    Type::Var(TypeVarId(idx as u32))
                }
            })
            .collect();
        let row = RowType {
            fields: info
                .row
                .fields
                .iter()
                .map(|(label, ty)| {
                    (
                        label.clone(),
                        substitute_params(ty, &info.params, &replacements),
                    )
                })
                .collect(),
            rest: info.row.rest,
        };
        Some(Type::Record(RecordType {
            name: name.to_string(),
            params: replacements,
            row,
        }))
    }

    /// List all registered record names.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.records.keys().map(|s| s.as_str())
    }

    /// List all registered alias names.
    pub fn alias_names(&self) -> impl Iterator<Item = &str> {
        self.aliases.keys().map(|s| s.as_str())
    }

    /// List all registered opaque type names.
    pub fn opaque_names(&self) -> impl Iterator<Item = &str> {
        self.opaques.keys().map(|s| s.as_str())
    }

    /// Merge a record from an imported module. Fails on name conflict.
    pub fn merge_record(&mut self, name: String, info: RecordInfo) -> Result<(), String> {
        if self.records.contains_key(&name)
            || self.aliases.contains_key(&name)
            || self.opaques.contains_key(&name)
        {
            return Err(format!("type `{name}` is already defined"));
        }
        self.records.insert(name, info);
        Ok(())
    }

    /// Merge an alias from an imported module. Fails on name conflict.
    pub fn merge_alias(&mut self, name: String, info: AliasInfo) -> Result<(), String> {
        if self.records.contains_key(&name)
            || self.aliases.contains_key(&name)
            || self.opaques.contains_key(&name)
        {
            return Err(format!("type `{name}` is already defined"));
        }
        self.aliases.insert(name, info);
        Ok(())
    }

    /// Merge an opaque type from an imported module. Fails on name conflict.
    pub fn merge_opaque(&mut self, name: String, info: OpaqueTypeInfo) -> Result<(), String> {
        if self.records.contains_key(&name)
            || self.aliases.contains_key(&name)
            || self.opaques.contains_key(&name)
        {
            return Err(format!("type `{name}` is already defined"));
        }
        self.opaques.insert(name, info);
        Ok(())
    }

    fn alias_has_cycle(&self) -> bool {
        fn visit(
            name: &str,
            aliases: &BTreeMap<String, AliasInfo>,
            visiting: &mut BTreeSet<String>,
            visited: &mut BTreeSet<String>,
        ) -> bool {
            if visited.contains(name) {
                return false;
            }
            if !visiting.insert(name.to_string()) {
                return true;
            }
            let Some(info) = aliases.get(name) else {
                visiting.remove(name);
                return false;
            };
            let mut deps = BTreeSet::new();
            collect_annotation_named_types(&info.target, &mut deps);
            for dep in deps {
                if aliases.contains_key(&dep) && visit(&dep, aliases, visiting, visited) {
                    return true;
                }
            }
            visiting.remove(name);
            visited.insert(name.to_string());
            false
        }

        let mut visiting = BTreeSet::new();
        let mut visited = BTreeSet::new();
        for name in self.aliases.keys() {
            if visit(name, &self.aliases, &mut visiting, &mut visited) {
                return true;
            }
        }
        false
    }
}

impl Default for RecordRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Sum type registry
// ---------------------------------------------------------------------------

/// Type-level information about a sum type variant.
#[derive(Debug, Clone)]
pub struct VariantInfo {
    pub name: String,
    pub fields: Vec<VariantFieldInfo>,
    /// Variant-local type equalities from `where` clauses.
    pub where_constraints: Vec<(Type, Type)>,
    /// Per-field flag indicating whether this field participates in the
    /// current strongly-connected recursive type component.
    pub recursive_fields: Vec<bool>,
    /// Source span of the variant name in its definition.
    pub definition_span: Option<Span>,
}

#[derive(Debug, Clone)]
pub struct VariantFieldInfo {
    pub name: Option<String>,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct InstantiatedVariant {
    pub sum_type: Type,
    pub field_types: Vec<VariantFieldInfo>,
    pub where_constraints: Vec<(Type, Type)>,
}

/// Type-level information about a named sum type.
#[derive(Debug, Clone)]
pub struct SumTypeInfo {
    pub params: Vec<String>,
    pub variants: Vec<VariantInfo>,
    /// True when this type is self-recursive or mutually recursive.
    pub is_recursive: bool,
    /// Source span of the type name in its definition.
    pub definition_span: Option<Span>,
    /// Doc comment from `///` above the type definition.
    pub doc: Option<String>,
    /// Whether this type was declared `pub`.
    pub public: bool,
}

/// Result of resolving a variant name, possibly disambiguated by an expected type.
#[derive(Debug, Clone)]
pub enum VariantResolution {
    /// Exactly one match — unambiguous or expected type resolved it.
    Unique(String, VariantInfo),
    /// Multiple types define this constructor and no expected type to disambiguate.
    Ambiguous(Vec<String>),
    /// No type defines this constructor.
    NotFound,
}

/// Registry of user-defined sum type definitions.
///
/// Maps type names to their definitions and variant names back to their
/// owning type for constructor lookup.
#[derive(Debug, Clone)]
pub struct SumTypeRegistry {
    types: BTreeMap<String, SumTypeInfo>,
    /// Variant name → owning type name(s), for constructor resolution.
    /// A variant may map to multiple types when different sum types share
    /// the same constructor name (scoped constructors).
    variant_to_types: BTreeMap<String, Vec<String>>,
}

impl SumTypeRegistry {
    pub fn new() -> Self {
        let mut registry = Self {
            types: BTreeMap::new(),
            variant_to_types: BTreeMap::new(),
        };
        registry.register_builtin_sum_types();
        registry
    }

    fn register_builtin_sum_types(&mut self) {
        let mut builtin_names = Vec::new();
        builtin_names.extend(kea_types::BUILTIN_ERROR_TYPE_NAMES);
        builtin_names.extend(kea_types::BUILTIN_PROTOCOL_TYPE_NAMES);

        for name in builtin_names {
            let Some(Type::Sum(sum)) = kea_types::builtin_sum_type(name) else {
                continue;
            };

            let variants = sum
                .variants
                .iter()
                .map(|(variant_name, fields)| VariantInfo {
                    name: variant_name.clone(),
                    fields: fields
                        .iter()
                        .map(|ty| VariantFieldInfo {
                            name: None,
                            ty: ty.clone(),
                        })
                        .collect(),
                    where_constraints: vec![],
                    recursive_fields: vec![false; fields.len()],
                    definition_span: None,
                })
                .collect::<Vec<_>>();

            for variant in &variants {
                self.variant_to_types
                    .entry(variant.name.clone())
                    .or_default()
                    .push(name.to_string());
            }

            self.types.insert(
                name.to_string(),
                SumTypeInfo {
                    params: vec![],
                    variants,
                    is_recursive: false,
                    definition_span: None,
                    doc: Some(format!("Builtin sum type `{name}`.")),
                    public: true,
                },
            );
        }

        // Validated(T, E) = Valid(T) | Invalid(List(E))
        // Error-accumulating Applicative for collecting multiple validation errors.
        let validated_variants = vec![
            VariantInfo {
                name: "Valid".to_string(),
                fields: vec![VariantFieldInfo {
                    name: None,
                    ty: Type::Var(TypeVarId(0)),
                }],
                where_constraints: vec![],
                recursive_fields: vec![false],
                definition_span: None,
            },
            VariantInfo {
                name: "Invalid".to_string(),
                fields: vec![VariantFieldInfo {
                    name: None,
                    ty: Type::List(Box::new(Type::Var(TypeVarId(1)))),
                }],
                where_constraints: vec![],
                recursive_fields: vec![false],
                definition_span: None,
            },
        ];
        for variant in &validated_variants {
            self.variant_to_types
                .entry(variant.name.clone())
                .or_default()
                .push("Validated".to_string());
        }
        self.types.insert(
            "Validated".to_string(),
            SumTypeInfo {
                params: vec!["t".to_string(), "e".to_string()],
                variants: validated_variants,
                is_recursive: false,
                definition_span: None,
                doc: Some("Error-accumulating validation type. `Valid(t)` holds a success value, `Invalid(List(e))` accumulates errors.".to_string()),
                public: true,
            },
        );

        // Step(a) = Continue(a) | Halt(a)
        // Control type for fold_while short-circuit semantics.
        let step_variants = vec![
            VariantInfo {
                name: "Continue".to_string(),
                fields: vec![VariantFieldInfo {
                    name: None,
                    ty: Type::Var(TypeVarId(0)),
                }],
                where_constraints: vec![],
                recursive_fields: vec![false],
                definition_span: None,
            },
            VariantInfo {
                name: "Halt".to_string(),
                fields: vec![VariantFieldInfo {
                    name: None,
                    ty: Type::Var(TypeVarId(0)),
                }],
                where_constraints: vec![],
                recursive_fields: vec![false],
                definition_span: None,
            },
        ];
        for variant in &step_variants {
            self.variant_to_types
                .entry(variant.name.clone())
                .or_default()
                .push("Step".to_string());
        }
        self.types.insert(
            "Step".to_string(),
            SumTypeInfo {
                params: vec!["a".to_string()],
                variants: step_variants,
                is_recursive: false,
                definition_span: None,
                doc: Some("Control type for `fold_while`. `Continue(a)` keeps folding, `Halt(a)` stops early.".to_string()),
                public: true,
            },
        );

        // Seq(a) = Empty | Cons(a, fn() -> Seq(a)) | Suspend(fn() -> Seq(a))
        // Pure lazy sequence — replayable value, complement to Stream(T).
        let a_var = Type::Var(TypeVarId(0));
        let seq_of_a = Type::Sum(kea_types::SumType {
            name: "Seq".to_string(),
            type_args: vec![a_var.clone()],
            variants: vec![],
        });
        let thunk_to_seq = Type::Function(FunctionType {
            params: vec![],
            ret: Box::new(seq_of_a.clone()),
            effects: EffectRow::pure(),
        });
        let seq_variants = vec![
            VariantInfo {
                name: "SeqEmpty".to_string(),
                fields: vec![],
                where_constraints: vec![],
                recursive_fields: vec![],
                definition_span: None,
            },
            VariantInfo {
                name: "SeqCons".to_string(),
                fields: vec![
                    VariantFieldInfo {
                        name: None,
                        ty: a_var.clone(),
                    },
                    VariantFieldInfo {
                        name: None,
                        ty: thunk_to_seq.clone(),
                    },
                ],
                where_constraints: vec![],
                recursive_fields: vec![false, true],
                definition_span: None,
            },
            VariantInfo {
                name: "SeqSuspend".to_string(),
                fields: vec![VariantFieldInfo {
                    name: None,
                    ty: thunk_to_seq,
                }],
                where_constraints: vec![],
                recursive_fields: vec![true],
                definition_span: None,
            },
        ];
        for variant in &seq_variants {
            self.variant_to_types
                .entry(variant.name.clone())
                .or_default()
                .push("Seq".to_string());
        }
        self.types.insert(
            "Seq".to_string(),
            SumTypeInfo {
                params: vec!["a".to_string()],
                variants: seq_variants,
                is_recursive: true,
                definition_span: None,
                doc: Some("Pure lazy sequence. Replayable value — can be traversed multiple times. Complement to Stream(T) which is consumed once.".to_string()),
                public: true,
            },
        );
    }

    /// Register a sum type directly with pre-built info (for stdlib types
    /// that aren't parsed from source).
    pub fn register_raw(&mut self, name: &str, info: SumTypeInfo) {
        for variant in &info.variants {
            self.variant_to_types
                .entry(variant.name.clone())
                .or_default()
                .push(name.to_string());
        }
        self.types.insert(name.to_string(), info);
    }

    /// Register a sum type definition. Returns an error if variant names
    /// collide with other registered types.
    pub fn register(
        &mut self,
        def: &kea_ast::TypeDef,
        records: &RecordRegistry,
    ) -> Result<(), Diagnostic> {
        self.register_many(&[def], records)
    }

    /// Register a batch of sum type definitions in one pass.
    ///
    /// This supports self-recursive and mutually-recursive groups by first
    /// seeding all names, then resolving variant fields.
    pub fn register_many(
        &mut self,
        defs: &[&kea_ast::TypeDef],
        records: &RecordRegistry,
    ) -> Result<(), Diagnostic> {
        if defs.is_empty() {
            return Ok(());
        }

        // Pre-validate type-name collisions.
        let mut batch_names = BTreeSet::new();
        for def in defs {
            if self.types.contains_key(&def.name.node) {
                return Err(Diagnostic::error(
                    Category::TypeMismatch,
                    format!("type `{}` is already defined", def.name.node),
                )
                .at(SourceLocation {
                    file_id: def.name.span.file.0,
                    start: def.name.span.start,
                    end: def.name.span.end,
                }));
            }
            if !batch_names.insert(def.name.node.clone()) {
                return Err(Diagnostic::error(
                    Category::TypeMismatch,
                    format!("type `{}` is declared more than once", def.name.node),
                )
                .at(SourceLocation {
                    file_id: def.name.span.file.0,
                    start: def.name.span.start,
                    end: def.name.span.end,
                }));
            }
        }

        // Pre-validate: builtin constructors cannot be redefined.
        // Duplicate variant names across types are allowed (scoped constructors).
        let mut new_variant_to_type: BTreeMap<String, String> = BTreeMap::new();
        for def in defs {
            for variant in &def.variants {
                if matches!(variant.name.node.as_str(), "Some" | "None" | "Ok" | "Err") {
                    return Err(Diagnostic::error(
                        Category::TypeMismatch,
                        format!(
                            "variant `{}` shadows a builtin constructor",
                            variant.name.node,
                        ),
                    )
                    .at(SourceLocation {
                        file_id: variant.name.span.file.0,
                        start: variant.name.span.start,
                        end: variant.name.span.end,
                    }));
                }

                // Within the same batch, a variant name must be unique per type.
                // But the same name in different types is allowed.
                if let Some(existing_type) = new_variant_to_type.get(&variant.name.node)
                    && existing_type == &def.name.node
                {
                    return Err(Diagnostic::error(
                        Category::TypeMismatch,
                        format!(
                            "duplicate variant `{}` in type `{}`",
                            variant.name.node, existing_type,
                        ),
                    )
                    .at(SourceLocation {
                        file_id: variant.name.span.file.0,
                        start: variant.name.span.start,
                        end: variant.name.span.end,
                    }));
                }

                new_variant_to_type.insert(variant.name.node.clone(), def.name.node.clone());
            }
        }

        // Build type-dependency graph for recursion metadata.
        let dependency_graph = build_type_dependency_graph(defs);
        let component_map = strongly_connected_component_map(&dependency_graph);

        // Pass 1: seed all type names to allow recursive references.
        for def in defs {
            self.types.insert(
                def.name.node.clone(),
                SumTypeInfo {
                    params: def.params.clone(),
                    variants: Vec::new(),
                    is_recursive: false,
                    definition_span: Some(def.name.span),
                    doc: def.doc.clone(),
                    public: def.public,
                },
            );
        }

        // Pass 2: resolve all variant field types.
        let mut resolved_variants: BTreeMap<String, Vec<VariantInfo>> = BTreeMap::new();
        for def in defs {
            let type_param_scope: BTreeMap<String, Type> = def
                .params
                .iter()
                .enumerate()
                .map(|(idx, name)| (name.clone(), Type::Var(TypeVarId(idx as u32))))
                .collect();
            let mut variants = Vec::new();
            for variant in &def.variants {
                let mut fields = Vec::new();
                let mut where_constraints = Vec::new();
                let mut recursive_fields = Vec::new();
                let mut variant_field_named_types = BTreeSet::new();
                for field in &variant.fields {
                    if let Some(ty) = resolve_annotation_with_type_params(
                        &field.ty.node,
                        &type_param_scope,
                        records,
                        Some(self),
                    ) {
                        fields.push(VariantFieldInfo {
                            name: field.name.as_ref().map(|name| name.node.clone()),
                            ty,
                        });
                    } else {
                        // Roll back pass-1 placeholders on failure.
                        for seeded in defs {
                            self.types.remove(&seeded.name.node);
                        }
                        return Err(Diagnostic::error(
                            Category::TypeMismatch,
                            format!(
                                "unknown type in variant `{}` of type `{}`",
                                variant.name.node, def.name.node,
                            ),
                        )
                        .at(SourceLocation {
                            file_id: variant.name.span.file.0,
                            start: variant.name.span.start,
                            end: variant.name.span.end,
                        }));
                    }

                    let mut named = BTreeSet::new();
                    collect_annotation_named_types(&field.ty.node, &mut named);
                    variant_field_named_types.extend(named.iter().cloned());
                    let is_recursive_field = component_map
                        .get(&def.name.node)
                        .is_some_and(|component| named.iter().any(|dep| component.contains(dep)));
                    recursive_fields.push(is_recursive_field);
                }

                let mut constrained_params = BTreeSet::new();
                for where_item in &variant.where_clause {
                    let Some(param_index) = def
                        .params
                        .iter()
                        .position(|p| p == &where_item.type_var.node)
                    else {
                        for seeded in defs {
                            self.types.remove(&seeded.name.node);
                        }
                        return Err(Diagnostic::error(
                            Category::TypeMismatch,
                            format!(
                                "unknown type parameter `{}` in variant where clause",
                                where_item.type_var.node,
                            ),
                        )
                        .at(SourceLocation {
                            file_id: where_item.type_var.span.file.0,
                            start: where_item.type_var.span.start,
                            end: where_item.type_var.span.end,
                        }));
                    };

                    if !constrained_params.insert(param_index) {
                        for seeded in defs {
                            self.types.remove(&seeded.name.node);
                        }
                        return Err(Diagnostic::error(
                            Category::TypeMismatch,
                            format!(
                                "duplicate where-clause constraint for type parameter `{}`",
                                where_item.type_var.node,
                            ),
                        )
                        .at(SourceLocation {
                            file_id: where_item.type_var.span.file.0,
                            start: where_item.type_var.span.start,
                            end: where_item.type_var.span.end,
                        }));
                    }

                    let Some(rhs) = resolve_annotation_with_type_params(
                        &where_item.ty.node,
                        &type_param_scope,
                        records,
                        Some(self),
                    ) else {
                        for seeded in defs {
                            self.types.remove(&seeded.name.node);
                        }
                        return Err(Diagnostic::error(
                            Category::TypeMismatch,
                            format!(
                                "unknown type in variant where clause `{}`",
                                annotation_display(&where_item.ty.node),
                            ),
                        )
                        .at(SourceLocation {
                            file_id: where_item.ty.span.file.0,
                            start: where_item.ty.span.start,
                            end: where_item.ty.span.end,
                        }));
                    };

                    where_constraints.push((Type::Var(TypeVarId(param_index as u32)), rhs));
                }

                variants.push(VariantInfo {
                    name: variant.name.node.clone(),
                    fields,
                    where_constraints,
                    recursive_fields,
                    definition_span: Some(variant.name.span),
                });
            }
            resolved_variants.insert(def.name.node.clone(), variants);
        }

        // Commit resolved variants + recursion flags.
        for def in defs {
            let is_recursive = component_map.get(&def.name.node).is_some_and(|component| {
                component.len() > 1
                    || dependency_graph
                        .get(&def.name.node)
                        .is_some_and(|deps| deps.contains(&def.name.node))
            });

            if let Some(info) = self.types.get_mut(&def.name.node) {
                info.variants = resolved_variants.remove(&def.name.node).unwrap_or_default();
                info.is_recursive = is_recursive;
            }
        }

        for (variant, type_name) in new_variant_to_type {
            let types = self.variant_to_types.entry(variant).or_default();
            if !types.contains(&type_name) {
                types.push(type_name);
            }
        }

        Ok(())
    }

    /// Look up a sum type by name.
    pub fn lookup(&self, name: &str) -> Option<&SumTypeInfo> {
        self.types.get(name)
    }

    /// Iterate all registered sum types.
    pub fn all_types(&self) -> impl Iterator<Item = (&String, &SumTypeInfo)> {
        self.types.iter()
    }

    /// Look up a variant by name, returning (type_name, variant_info).
    ///
    /// When a variant name is shared across multiple types, returns the first
    /// (unambiguous only if there's exactly one). Use `resolve_variant` for
    /// disambiguation with an expected type.
    pub fn lookup_variant(&self, variant_name: &str) -> Option<(&str, &VariantInfo)> {
        let types = self.variant_to_types.get(variant_name)?;
        if types.len() != 1 {
            return None;
        }
        let type_name = &types[0];
        let info = self.types.get(type_name)?;
        let variant = info.variants.iter().find(|v| v.name == variant_name)?;
        Some((type_name, variant))
    }

    /// Look up a variant by name within a specific sum type.
    pub fn lookup_variant_in_type<'a>(
        &'a self,
        variant_name: &str,
        type_name: &str,
    ) -> Option<&'a VariantInfo> {
        let info = self.types.get(type_name)?;
        info.variants.iter().find(|v| v.name == variant_name)
    }

    /// Resolve a variant name, optionally disambiguating with an expected type.
    pub fn resolve_variant(
        &self,
        variant_name: &str,
        expected_type: Option<&str>,
    ) -> VariantResolution {
        let Some(types) = self.variant_to_types.get(variant_name) else {
            return VariantResolution::NotFound;
        };
        if types.is_empty() {
            return VariantResolution::NotFound;
        }
        if types.len() == 1 {
            let type_name = &types[0];
            if let Some(info) = self.types.get(type_name)
                && let Some(variant) = info.variants.iter().find(|v| v.name == variant_name)
            {
                return VariantResolution::Unique(type_name.clone(), variant.clone());
            }
            return VariantResolution::NotFound;
        }
        // Multiple types define this variant — try expected type disambiguation.
        if let Some(expected) = expected_type
            && types.contains(&expected.to_string())
            && let Some(info) = self.types.get(expected)
            && let Some(variant) = info.variants.iter().find(|v| v.name == variant_name)
        {
            return VariantResolution::Unique(expected.to_string(), variant.clone());
        }
        VariantResolution::Ambiguous(types.clone())
    }

    /// Check whether a variant name is registered (for any type).
    pub fn has_variant(&self, variant_name: &str) -> bool {
        self.variant_to_types
            .get(variant_name)
            .is_some_and(|types| !types.is_empty())
    }

    /// Instantiate a sum variant with fresh type variables.
    ///
    /// Returns the owning sum type, instantiated field types for this
    /// constructor, and instantiated variant where-clause constraints.
    ///
    /// When a variant is ambiguous, pass `expected_type` to disambiguate.
    pub fn instantiate_variant(
        &self,
        variant_name: &str,
        unifier: &mut Unifier,
    ) -> Option<InstantiatedVariant> {
        self.instantiate_variant_for_type(variant_name, None, unifier)
    }

    /// Instantiate a variant, optionally disambiguating with an expected type name.
    pub fn instantiate_variant_for_type(
        &self,
        variant_name: &str,
        expected_type: Option<&str>,
        unifier: &mut Unifier,
    ) -> Option<InstantiatedVariant> {
        let (type_name, variant) = match self.resolve_variant(variant_name, expected_type) {
            VariantResolution::Unique(tn, vi) => (tn, vi),
            _ => return None,
        };
        let info = self.lookup(&type_name)?;

        if info.params.is_empty() {
            let sum_ty = self.to_type(&type_name)?;
            return Some(InstantiatedVariant {
                sum_type: sum_ty,
                field_types: variant.fields.clone(),
                where_constraints: variant.where_constraints.clone(),
            });
        }

        let fresh_vars: Vec<Type> = info.params.iter().map(|_| unifier.fresh_type()).collect();
        let variants = info
            .variants
            .iter()
            .map(|v| {
                let fields = v
                    .fields
                    .iter()
                    .map(|field| substitute_params(&field.ty, &info.params, &fresh_vars))
                    .collect();
                (v.name.clone(), fields)
            })
            .collect();
        let sum_ty = Type::Sum(SumType {
            name: type_name.to_string(),
            type_args: fresh_vars.clone(),
            variants,
        });
        let field_types = variant
            .fields
            .iter()
            .map(|field| VariantFieldInfo {
                name: field.name.clone(),
                ty: substitute_params(&field.ty, &info.params, &fresh_vars),
            })
            .collect();
        let where_constraints = variant
            .where_constraints
            .iter()
            .map(|(lhs, rhs)| {
                (
                    substitute_params(lhs, &info.params, &fresh_vars),
                    substitute_params(rhs, &info.params, &fresh_vars),
                )
            })
            .collect();
        Some(InstantiatedVariant {
            sum_type: sum_ty,
            field_types,
            where_constraints,
        })
    }

    /// Convert a sum type name to its semantic type, substituting fresh
    /// type variables for any type parameters.
    pub fn to_type(&self, name: &str) -> Option<Type> {
        self.to_type_with(name, &mut None)
    }

    /// Convert with an optional unifier for fresh type var generation.
    /// If unifier is None, uses placeholder vars (for annotation resolution).
    pub fn to_type_with(&self, name: &str, unifier: &mut Option<&mut Unifier>) -> Option<Type> {
        let info = self.lookup(name)?;
        if info.params.is_empty() {
            // No params — return as-is
            let variants = info
                .variants
                .iter()
                .map(|v| {
                    (
                        v.name.clone(),
                        v.fields.iter().map(|field| field.ty.clone()).collect(),
                    )
                })
                .collect();
            return Some(Type::Sum(SumType {
                name: name.to_string(),
                type_args: vec![],
                variants,
            }));
        }

        // Create fresh type vars for each param
        let fresh_vars: Vec<Type> = info
            .params
            .iter()
            .map(|_| {
                if let Some(u) = unifier.as_mut() {
                    u.fresh_type()
                } else {
                    Type::Var(TypeVarId(u32::MAX)) // placeholder
                }
            })
            .collect();

        // Substitute param placeholder vars with fresh vars in variant fields
        let variants = info
            .variants
            .iter()
            .map(|v| {
                let fields = v
                    .fields
                    .iter()
                    .map(|field| substitute_params(&field.ty, &info.params, &fresh_vars))
                    .collect();
                (v.name.clone(), fields)
            })
            .collect();

        Some(Type::Sum(SumType {
            name: name.to_string(),
            type_args: fresh_vars.clone(),
            variants,
        }))
    }

    /// List all registered sum type names.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.types.keys().map(|s| s.as_str())
    }

    /// Return whether a named sum type is recursive.
    pub fn is_recursive_type(&self, name: &str) -> bool {
        self.types.get(name).is_some_and(|info| info.is_recursive)
    }

    /// Merge a sum type from an imported module. Fails on type name conflict.
    ///
    /// Variant name collisions across types are allowed (scoped constructors).
    pub fn merge_type(&mut self, name: String, info: SumTypeInfo) -> Result<(), String> {
        if self.types.contains_key(&name) {
            return Err(format!("type `{name}` is already defined"));
        }
        for variant in &info.variants {
            let types = self.variant_to_types.entry(variant.name.clone()).or_default();
            if !types.contains(&name) {
                types.push(name.clone());
            }
        }
        self.types.insert(name, info);
        Ok(())
    }
}

impl Default for SumTypeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Substitute type parameter placeholders with concrete types.
fn substitute_params(ty: &Type, params: &[String], replacements: &[Type]) -> Type {
    let bindings: BTreeMap<String, Type> = params
        .iter()
        .cloned()
        .zip(replacements.iter().cloned())
        .collect();
    instantiate_impl_type(ty, params, &bindings)
}

// ---------------------------------------------------------------------------
// Trait registry
// ---------------------------------------------------------------------------

/// Information about a trait's method signature (type-level).
#[derive(Debug, Clone)]
pub struct TraitMethodInfo {
    pub name: String,
    /// Original parameter declarations (names + annotations) from the trait AST.
    pub params: Vec<kea_ast::Param>,
    /// Parameter types. `self` is represented as a type variable
    /// that will be substituted with the impl's concrete type.
    pub param_types: Vec<Type>,
    pub return_type: Type,
    /// Method-local + trait-level bounds captured from the method where-clause.
    /// Keys are placeholder type vars appearing in `param_types` / `return_type`.
    pub method_bounds: BTreeMap<TypeVarId, BTreeSet<String>>,
    /// Method-local + trait-level kind map for placeholder type vars.
    pub method_kinds: BTreeMap<TypeVarId, Kind>,
    /// Optional default method body declared in the trait.
    pub default_body: Option<kea_ast::Expr>,
    /// Optional effect contract declared on the trait method.
    pub declared_effect: Option<kea_ast::EffectAnnotation>,
    /// Doc comment from `///` above the trait method.
    pub doc: Option<String>,
}

/// Associated type declared in a trait definition.
#[derive(Debug, Clone)]
pub struct AssocTypeInfo {
    pub name: String,
    pub constraints: Vec<String>,
    pub default: Option<kea_ast::TypeAnnotation>,
}

/// Functional dependency declaration stored on a trait.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionalDependency {
    pub from: Vec<String>,
    pub to: Vec<String>,
}

/// Type-constructor parameter declared on a trait, with kind.
#[derive(Debug, Clone)]
pub struct TraitTypeParamInfo {
    pub name: String,
    pub kind: Kind,
}

/// Information about a registered trait.
#[derive(Debug, Clone)]
pub struct TraitInfo {
    pub name: String,
    /// Type-constructor parameters for higher-kinded traits.
    pub type_params: Vec<TraitTypeParamInfo>,
    /// Direct supertraits declared as `trait T: A + B { ... }`.
    pub supertraits: Vec<String>,
    pub methods: Vec<TraitMethodInfo>,
    /// Associated types declared in the trait (`type Source`, etc.).
    pub associated_types: Vec<AssocTypeInfo>,
    /// Functional dependencies declared on the trait (`| A -> B`).
    pub fundeps: Vec<FunctionalDependency>,
    /// Source span of the trait name in its definition.
    pub definition_span: Option<Span>,
    /// Doc comment from `///` above the trait definition.
    pub doc: Option<String>,
}

/// Information about a trait implementation.
#[derive(Debug, Clone)]
pub struct ImplInfo {
    pub trait_name: String,
    pub type_name: String,
    /// Type parameters declared in the impl header (`impl Show for List(t)`).
    pub type_params: Vec<String>,
    /// Trait bounds on impl type parameters (`t: Show`).
    pub param_bounds: BTreeMap<String, Vec<String>>,
    /// Resolved method implementations: name → function type.
    pub methods: BTreeMap<String, Type>,
    /// Associated type assignments (e.g., "Source" → String) from where clause.
    pub associated_types: BTreeMap<String, Type>,
    /// Registration source (manual, builtin, derive, conditional).
    pub via: ImplVia,
}

/// Source of a trait impl registration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImplVia {
    Builtin,
    Manual,
    Derive,
    Conditional,
}

impl ImplVia {
    pub fn as_str(self) -> &'static str {
        match self {
            ImplVia::Builtin => "builtin",
            ImplVia::Manual => "manual",
            ImplVia::Derive => "derive",
            ImplVia::Conditional => "conditional",
        }
    }
}

/// A trait-solver goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraitGoal {
    /// Prove that `ty` implements `trait_name`.
    Implements { trait_name: String, ty: Type },
    /// Prove a projection equality (`base_ty.Assoc = rhs`) under `base_trait`.
    ProjectionEq {
        base_trait: String,
        base_ty: Type,
        assoc: String,
        rhs: Type,
    },
}

/// Why a trait goal could not be solved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MismatchReason {
    UnknownTrait {
        trait_name: String,
    },
    NotATypeConstructor {
        ty: Type,
    },
    NoImplForConstructor {
        trait_name: String,
        type_constructor: String,
    },
    TypeArgArityMismatch {
        expected: usize,
        got: usize,
    },
    MissingAssociatedType {
        assoc: String,
    },
    AssocTypeMismatch {
        assoc: String,
        expected: Type,
        found: Type,
    },
    FundepConflict {
        dependency: String,
    },
    ParamBoundUnsatisfied {
        param: String,
        bound_trait: String,
        ty: Type,
    },
    ParamBoundAmbiguous {
        param: String,
        bound_trait: String,
        ty: Type,
    },
    SupertraitUnsatisfied {
        supertrait: String,
        ty: Type,
    },
    SupertraitAmbiguous {
        supertrait: String,
        ty: Type,
    },
}

/// A solved trait candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolvedCandidate {
    /// Index into `TraitRegistry::impls` when backed by an impl; `None` for
    /// synthetic proofs (for example existential bounds).
    pub impl_index: Option<usize>,
    pub trait_name: String,
    pub type_name: String,
    pub bindings: BTreeMap<String, Type>,
    pub associated_types: BTreeMap<String, Type>,
    pub nested_obligations: Vec<(String, Type)>,
}

/// Outcome of solving a trait goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolveOutcome {
    Unique(SolvedCandidate),
    Ambiguous(Vec<SolvedCandidate>),
    NoMatch(Vec<MismatchReason>),
}

/// How a method is dispatched in the actor message loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DispatchSemantics {
    /// Returns Self → fire-and-forget state update (send).
    Send,
    /// Returns a value (not Self) → read-only query (call).
    CallPure,
    /// Returns #(Self, T) → state update + reply (call).
    CallWithState,
}

/// Type information for a single actor method, as seen by send/call dispatch.
#[derive(Debug, Clone)]
pub struct MethodProtocol {
    /// Parameter types excluding `self`.
    pub params: Vec<Type>,
    /// The method's return type.
    pub return_type: Type,
    /// How this method should be dispatched.
    pub semantics: DispatchSemantics,
}

/// The complete protocol (set of methods) for an actor type.
#[derive(Debug, Clone)]
pub struct ActorProtocol {
    pub type_name: String,
    pub methods: BTreeMap<String, MethodProtocol>,
    /// The control channel signal type, if `type Control = X` was declared.
    pub control_type: Option<Type>,
}

/// Derive dispatch semantics from a method's return type relative to its type name.
///
/// Rules (KERNEL.md §13.5):
/// - Returns `Self` (same named record) → `Send`
/// - Returns `#(Self, T)` → `CallWithState`
/// - Returns anything else → `CallPure`
/// - Unresolved `Var(_)` → `CallPure` (safest default)
///
/// Takes `type_name` directly rather than the self type, because generalized
/// method types have structural `AnonRecord` self parameters (from row polymorphism)
/// while return type annotations preserve nominal `Record` types.
pub fn derive_dispatch_semantics(type_name: &str, return_type: &Type) -> DispatchSemantics {
    match return_type {
        // Returns exactly Self (same named Record type) → Send
        Type::Record(ret_rec) if ret_rec.name == type_name => DispatchSemantics::Send,
        // Method inference may erase nominal identity to a structural record;
        // in actor impls this still represents updated self state.
        Type::AnonRecord(_) => DispatchSemantics::Send,

        // Returns #(Self, T) → CallWithState
        Type::Tuple(elems)
            if elems.len() == 2
                && matches!(&elems[0], Type::Record(first_rec) if first_rec.name == type_name) =>
        {
            DispatchSemantics::CallWithState
        }

        // Unresolved type variable — default to CallPure (safest: no state mutation assumed)
        Type::Var(_) => DispatchSemantics::CallPure,

        // Anything else → CallPure
        _ => DispatchSemantics::CallPure,
    }
}

fn ast_kind_to_kind(kind: &kea_ast::KindAnnotation) -> Kind {
    match kind {
        kea_ast::KindAnnotation::Star => Kind::Star,
    }
}

fn next_placeholder_type_var(next_placeholder: &mut u32) -> TypeVarId {
    let id = TypeVarId(*next_placeholder);
    *next_placeholder = next_placeholder.wrapping_sub(1);
    id
}

fn trait_self_type_param_index(type_params: &[kea_ast::TraitTypeParam]) -> Option<usize> {
    type_params
        .iter()
        .position(|param| param.name.node == "Self")
        .or_else(|| (!type_params.is_empty()).then_some(0))
}

fn trait_self_param_info(trait_info: &TraitInfo) -> Option<&TraitTypeParamInfo> {
    trait_info
        .type_params
        .iter()
        .find(|param| param.name == "Self")
        .or_else(|| trait_info.type_params.first())
}

fn trait_self_alias(trait_info: &TraitInfo) -> Option<&str> {
    trait_self_param_info(trait_info).map(|param| param.name.as_str())
}

fn where_trait_bound_kind(
    traits: &TraitRegistry,
    bound_type_var: &kea_ast::Spanned<String>,
    trait_name: &kea_ast::Spanned<String>,
    context: &str,
) -> Result<Kind, Diagnostic> {
    let Some(info) = traits.lookup_trait(&trait_name.node) else {
        return Err(Diagnostic::error(
            Category::TraitBound,
            format!("trait `{}` is not defined", trait_name.node),
        )
        .at(span_to_loc(trait_name.span))
        .with_help(format!("invalid trait bound in {context}")));
    };

    if info.type_params.is_empty() {
        return Ok(Kind::Star);
    }
    if info.type_params.len() == 1 {
        return Ok(info.type_params[0].kind.clone());
    }

    if let Some(param) = info
        .type_params
        .iter()
        .find(|param| param.name == bound_type_var.node)
    {
        return Ok(param.kind.clone());
    }

    let names = info
        .type_params
        .iter()
        .map(|param| format!("`{}`", param.name))
        .collect::<Vec<_>>()
        .join(", ");
    Err(Diagnostic::error(
        Category::TypeError,
        format!(
            "ambiguous bound `{}`: trait `{}` has multiple type parameters",
            bound_type_var.node, trait_name.node
        ),
    )
    .at(span_to_loc(bound_type_var.span))
    .with_help(format!(
        "use one of the trait parameter names in the where clause: {names}"
    )))
}

pub fn validate_where_clause_traits(
    where_clause: &[kea_ast::TraitBound],
    traits: &TraitRegistry,
) -> Vec<Diagnostic> {
    where_clause
        .iter()
        .filter_map(|bound| {
            where_trait_bound_kind(traits, &bound.type_var, &bound.trait_name, "where clauses")
                .err()
        })
        .collect()
}

fn format_fundep(dependency: &FunctionalDependency) -> String {
    let format_side = |names: &[String]| {
        if names.len() == 1 {
            names[0].clone()
        } else {
            format!("({})", names.join(", "))
        }
    };
    format!(
        "{} -> {}",
        format_side(&dependency.from),
        format_side(&dependency.to)
    )
}

fn validate_trait_fundeps(
    def: &kea_ast::TraitDef,
) -> Result<Vec<FunctionalDependency>, Diagnostic> {
    if def.fundeps.is_empty() {
        return Ok(Vec::new());
    }

    let type_param_names: BTreeSet<String> = def
        .type_params
        .iter()
        .map(|p| p.name.node.clone())
        .collect();
    let assoc_names: BTreeSet<String> = def
        .associated_types
        .iter()
        .map(|a| a.name.node.clone())
        .collect();

    let mut seen = BTreeSet::new();
    let mut validated = Vec::new();

    for fd in &def.fundeps {
        let from: Vec<String> = fd.from.iter().map(|n| n.node.clone()).collect();
        let to: Vec<String> = fd.to.iter().map(|n| n.node.clone()).collect();

        let mut seen_from = BTreeSet::new();
        for name in &from {
            if !seen_from.insert(name.clone()) {
                return Err(Diagnostic::error(
                    Category::TypeError,
                    format!("duplicate parameter `{name}` in functional dependency"),
                )
                .at(span_to_loc(def.name.span)));
            }
        }

        let mut seen_to = BTreeSet::new();
        for name in &to {
            if !seen_to.insert(name.clone()) {
                return Err(Diagnostic::error(
                    Category::TypeError,
                    format!("duplicate parameter `{name}` in functional dependency"),
                )
                .at(span_to_loc(def.name.span)));
            }
        }

        for name in from.iter().chain(to.iter()) {
            if !type_param_names.contains(name) && !assoc_names.contains(name) {
                return Err(Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "functional dependency references unknown parameter or associated type `{name}`"
                    ),
                )
                .at(span_to_loc(def.name.span)));
            }
        }

        if from.iter().any(|p| to.contains(p)) {
            return Err(Diagnostic::error(
                Category::TypeError,
                format!(
                    "functional dependency `{}` is cyclic",
                    format_fundep(&FunctionalDependency {
                        from: from.clone(),
                        to: to.clone()
                    })
                ),
            )
            .at(span_to_loc(def.name.span)));
        }

        let canonical = (from.clone(), to.clone());
        if !seen.insert(canonical) {
            return Err(Diagnostic::error(
                Category::TypeError,
                format!(
                    "duplicate functional dependency `{}`",
                    format_fundep(&FunctionalDependency { from, to })
                ),
            )
            .at(span_to_loc(def.name.span)));
        }

        validated.push(FunctionalDependency { from, to });
    }

    Ok(validated)
}

fn validate_self_projection_targets(
    ann: &TypeAnnotation,
    declared_assoc_types: &BTreeSet<String>,
    span: Span,
    context: &str,
) -> Result<(), Diagnostic> {
    fn walk(
        ann: &TypeAnnotation,
        declared_assoc_types: &BTreeSet<String>,
        span: Span,
        context: &str,
    ) -> Result<(), Diagnostic> {
        match ann {
            TypeAnnotation::Projection { base, name } => {
                if base == "Self" && !declared_assoc_types.contains(name) {
                    return Err(Diagnostic::error(
                        Category::TypeError,
                        format!("unknown associated type `{name}` referenced in `{context}`"),
                    )
                    .at(span_to_loc(span))
                    .with_help(format!(
                        "available associated types: {}",
                        declared_assoc_types
                            .iter()
                            .map(|n| format!("`{n}`"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )));
                }
                Ok(())
            }
            TypeAnnotation::Applied(_, args) => {
                for arg in args {
                    walk(arg, declared_assoc_types, span, context)?;
                }
                Ok(())
            }
            TypeAnnotation::Row { fields, .. } => {
                for (_, field_ty) in fields {
                    walk(field_ty, declared_assoc_types, span, context)?;
                }
                Ok(())
            }
            TypeAnnotation::EffectRow(_) => Ok(()),
            TypeAnnotation::Tuple(elems) => {
                for elem in elems {
                    walk(elem, declared_assoc_types, span, context)?;
                }
                Ok(())
            }
            TypeAnnotation::Forall { ty, .. } => walk(ty, declared_assoc_types, span, context),
            TypeAnnotation::Function(params, ret)
            | TypeAnnotation::FunctionWithEffect(params, _, ret) => {
                for param in params {
                    walk(param, declared_assoc_types, span, context)?;
                }
                walk(ret, declared_assoc_types, span, context)
            }
            TypeAnnotation::Optional(inner) => walk(inner, declared_assoc_types, span, context),
            TypeAnnotation::Existential {
                associated_types, ..
            } => {
                for (_, ann) in associated_types {
                    walk(ann, declared_assoc_types, span, context)?;
                }
                Ok(())
            }
            TypeAnnotation::Named(_) | TypeAnnotation::DimLiteral(_) => Ok(()),
        }
    }

    walk(ann, declared_assoc_types, span, context)
}

fn fundep_symbol_value(
    symbol: &str,
    trait_info: &TraitInfo,
    type_name: &str,
    type_params: &[String],
    associated_types: &BTreeMap<String, Type>,
) -> Option<Type> {
    let self_alias = trait_self_alias(trait_info);
    if symbol == "Self" || self_alias == Some(symbol) {
        let args: Vec<Type> = type_params
            .iter()
            .enumerate()
            .map(|(i, _)| Type::Var(TypeVarId(i as u32)))
            .collect();
        return Some(rebuild_type(type_name, &args).unwrap_or_else(|| {
            Type::App(
                Box::new(Type::Constructor {
                    name: type_name.to_string(),
                    fixed_args: Vec::new(),
                    arity: args.len(),
                }),
                args,
            )
        }));
    }

    if let Some(pos) = type_params.iter().position(|p| p == symbol) {
        return Some(Type::Var(TypeVarId(pos as u32)));
    }

    associated_types.get(symbol).cloned()
}

fn fundep_side_values(
    names: &[String],
    trait_info: &TraitInfo,
    type_name: &str,
    type_params: &[String],
    associated_types: &BTreeMap<String, Type>,
) -> Option<Vec<Type>> {
    names
        .iter()
        .map(|name| fundep_symbol_value(name, trait_info, type_name, type_params, associated_types))
        .collect()
}

fn resolve_assoc_annotation_for_impl(
    ann: &TypeAnnotation,
    type_name: &str,
    type_params: &[String],
    associated_types: &BTreeMap<String, Type>,
) -> Option<Type> {
    let empty_records = RecordRegistry::new();
    let mut param_scope: BTreeMap<String, Type> = type_params
        .iter()
        .enumerate()
        .map(|(i, p)| (p.clone(), Type::Var(TypeVarId(i as u32))))
        .collect();
    let args: Vec<Type> = type_params
        .iter()
        .enumerate()
        .map(|(i, _)| Type::Var(TypeVarId(i as u32)))
        .collect();
    let self_type = rebuild_type(type_name, &args).unwrap_or_else(|| {
        Type::App(
            Box::new(Type::Constructor {
                name: type_name.to_string(),
                fixed_args: Vec::new(),
                arity: args.len(),
            }),
            args.clone(),
        )
    });
    let mut placeholder_id = u32::MAX;
    resolve_annotation_with_self_assoc_and_params(
        ann,
        &empty_records,
        &self_type,
        associated_types,
        &mut param_scope,
        &mut placeholder_id,
    )
}

fn infer_impl_target_kind(type_name: &str, type_params: &[String]) -> Kind {
    let _ = builtin_type_constructor_arity(type_name);
    let _ = type_params;
    Kind::Star
}

/// Registry of trait definitions and implementations.
///
/// Handles trait registration, coherence checking, and method dispatch.
#[derive(Debug, Clone)]
pub struct TraitRegistry {
    traits: BTreeMap<String, TraitInfo>,
    impls: Vec<ImplInfo>,
    actor_protocols: Vec<ActorProtocol>,
    trait_owners: BTreeMap<String, String>,
    type_owners: BTreeMap<String, String>,
}

impl TraitRegistry {
    pub fn new() -> Self {
        Self {
            traits: BTreeMap::new(),
            impls: Vec::new(),
            actor_protocols: Vec::new(),
            trait_owners: BTreeMap::new(),
            type_owners: BTreeMap::new(),
        }
    }

    /// Register a trait definition from its AST.
    pub fn register_trait(
        &mut self,
        def: &kea_ast::TraitDef,
        records: &RecordRegistry,
    ) -> Result<(), Diagnostic> {
        self.register_trait_with_owner(def, records, "repl:")
    }

    /// Register a trait definition with an explicit owning module.
    pub fn register_trait_with_owner(
        &mut self,
        def: &kea_ast::TraitDef,
        records: &RecordRegistry,
        owner_module: &str,
    ) -> Result<(), Diagnostic> {
        if self.traits.contains_key(&def.name.node) {
            return Err(Diagnostic::error(
                Category::TypeError,
                format!("trait `{}` is already defined", def.name.node),
            )
            .at(SourceLocation {
                file_id: def.name.span.file.0,
                start: def.name.span.start,
                end: def.name.span.end,
            }));
        }

        let mut seen_supertraits = std::collections::BTreeSet::new();
        let mut supertraits = Vec::new();
        for supertrait in &def.supertraits {
            if supertrait.node == def.name.node {
                return Err(Diagnostic::error(
                    Category::TypeError,
                    format!("trait `{}` cannot inherit from itself", def.name.node),
                )
                .at(SourceLocation {
                    file_id: supertrait.span.file.0,
                    start: supertrait.span.start,
                    end: supertrait.span.end,
                }));
            }

            if !seen_supertraits.insert(supertrait.node.clone()) {
                return Err(Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "duplicate supertrait `{}` in trait `{}`",
                        supertrait.node, def.name.node
                    ),
                )
                .at(SourceLocation {
                    file_id: supertrait.span.file.0,
                    start: supertrait.span.start,
                    end: supertrait.span.end,
                }));
            }

            if !self.traits.contains_key(&supertrait.node) {
                return Err(Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "unknown supertrait `{}` in trait `{}`",
                        supertrait.node, def.name.node
                    ),
                )
                .at(SourceLocation {
                    file_id: supertrait.span.file.0,
                    start: supertrait.span.start,
                    end: supertrait.span.end,
                }));
            }
            supertraits.push(supertrait.node.clone());
        }
        let fundeps = validate_trait_fundeps(def)?;
        let declared_assoc_type_names: BTreeSet<String> = def
            .associated_types
            .iter()
            .map(|at| at.name.node.clone())
            .collect();
        for at in &def.associated_types {
            if let Some(default_ann) = &at.default {
                validate_self_projection_targets(
                    &default_ann.node,
                    &declared_assoc_type_names,
                    default_ann.span,
                    "associated type default",
                )?;
            }
        }

        let mut methods = Vec::new();
        // Placeholder type vars for trait method params use IDs counting down
        // from u32::MAX to avoid collision with the inference engine's counter
        // (which counts up from 0). Each unannotated param gets a distinct ID.
        let mut placeholder_id = u32::MAX.wrapping_sub(1);
        // Self maps to a fixed placeholder shared across methods.
        let self_type_var = TypeVarId(u32::MAX);
        let self_type = Type::Var(self_type_var);
        // Trait type constructor parameters are available in method signatures.
        // The dispatch parameter (named `Self`, otherwise the first trait type
        // parameter) reuses the Self placeholder so trait-method instantiation
        // can attach the trait bound to the constructor variable.
        let mut trait_type_placeholders: BTreeMap<String, Type> = BTreeMap::new();
        let mut trait_type_kinds: BTreeMap<TypeVarId, Kind> = BTreeMap::new();
        trait_type_placeholders.insert("Self".to_string(), self_type.clone());
        let self_param_idx = trait_self_type_param_index(&def.type_params);
        let self_kind = self_param_idx
            .map(|idx| ast_kind_to_kind(&def.type_params[idx].kind))
            .unwrap_or(Kind::Star);
        trait_type_kinds.insert(self_type_var, self_kind);
        if let Some(idx) = self_param_idx {
            trait_type_placeholders
                .insert(def.type_params[idx].name.node.clone(), self_type.clone());
        }
        for (idx, param) in def.type_params.iter().enumerate() {
            if Some(idx) == self_param_idx {
                continue;
            }
            let tv = next_placeholder_type_var(&mut placeholder_id);
            trait_type_placeholders.insert(param.name.node.clone(), Type::Var(tv));
            trait_type_kinds.insert(tv, ast_kind_to_kind(&param.kind));
        }
        // Each associated type gets a distinct placeholder type variable.
        let mut assoc_type_placeholders: BTreeMap<String, Type> = BTreeMap::new();
        for at in &def.associated_types {
            let tv = next_placeholder_type_var(&mut placeholder_id);
            assoc_type_placeholders.insert(at.name.node.clone(), Type::Var(tv));
        }
        for method in &def.methods {
            let mut method_type_params = trait_type_placeholders.clone();
            let mut method_bounds: BTreeMap<TypeVarId, BTreeSet<String>> = BTreeMap::new();
            let mut method_kinds = trait_type_kinds.clone();
            let declared_effect = match &method.effect_annotation {
                Some(ann) => {
                    let parsed = parse_effect_annotation(ann);
                    if let kea_ast::EffectAnnotation::Var(name) = &parsed
                        && !effect_var_is_constrained(name, &method.params)
                    {
                        return Err(Diagnostic::error(
                            Category::TypeMismatch,
                            format!(
                                "effect variable `{name}` is unconstrained in trait method `{}`; \
tie it to at least one function-typed parameter effect annotation",
                                method.name.node
                            ),
                        )
                        .at(span_to_loc(ann.span)));
                    }
                    Some(parsed)
                }
                None => None,
            };
            for bound in &method.where_clause {
                let expected_kind = where_trait_bound_kind(
                    self,
                    &bound.type_var,
                    &bound.trait_name,
                    "trait method where clauses",
                )?;
                let tv = match method_type_params.get(&bound.type_var.node) {
                    Some(Type::Var(existing_tv)) => {
                        if let Some(existing_kind) = method_kinds.get(existing_tv)
                            && existing_kind != &expected_kind
                        {
                            return Err(Diagnostic::error(
                                Category::TypeError,
                                format!(
                                    "kind mismatch for `{}` in where clause: expected {}, got {}",
                                    bound.type_var.node, existing_kind, expected_kind
                                ),
                            )
                            .at(span_to_loc(bound.type_var.span)));
                        }
                        *existing_tv
                    }
                    _ => {
                        let fresh = next_placeholder_type_var(&mut placeholder_id);
                        method_type_params.insert(bound.type_var.node.clone(), Type::Var(fresh));
                        method_kinds.insert(fresh, expected_kind.clone());
                        fresh
                    }
                };
                method_bounds
                    .entry(tv)
                    .or_default()
                    .insert(bound.trait_name.node.clone());
            }

            let mut param_types = Vec::new();
            for param in &method.params {
                if param.name() == Some("self") {
                    // `self` gets a placeholder — resolved per-impl.
                    // All self params across methods share the same ID (u32::MAX)
                    // since Self is one type within a trait.
                    param_types.push(self_type.clone());
                } else if let Some(ann) = &param.annotation {
                    match resolve_annotation_with_self_assoc_and_params(
                        &ann.node,
                        records,
                        &self_type,
                        &assoc_type_placeholders,
                        &mut method_type_params,
                        &mut placeholder_id,
                    ) {
                        Some(ty) => param_types.push(ty),
                        None => {
                            return Err(Diagnostic::error(
                                Category::TypeMismatch,
                                format!(
                                    "unknown type in parameter `{}` of trait method `{}`",
                                    param.name().unwrap_or("_"),
                                    method.name.node
                                ),
                            )
                            .at(SourceLocation {
                                file_id: param.pattern.span.file.0,
                                start: param.pattern.span.start,
                                end: param.pattern.span.end,
                            }));
                        }
                    }
                } else {
                    // Each unannotated param gets a distinct placeholder ID
                    let tv = next_placeholder_type_var(&mut placeholder_id);
                    param_types.push(Type::Var(tv));
                }
            }

            let return_type = if let Some(ann) = &method.return_annotation {
                match resolve_annotation_with_self_assoc_and_params(
                    &ann.node,
                    records,
                    &self_type,
                    &assoc_type_placeholders,
                    &mut method_type_params,
                    &mut placeholder_id,
                ) {
                    Some(ty) => ty,
                    None => {
                        return Err(Diagnostic::error(
                            Category::TypeMismatch,
                            format!("unknown return type in trait method `{}`", method.name.node),
                        )
                        .at(SourceLocation {
                            file_id: method.name.span.file.0,
                            start: method.name.span.start,
                            end: method.name.span.end,
                        }));
                    }
                }
            } else {
                Type::Unit
            };

            methods.push(TraitMethodInfo {
                name: method.name.node.clone(),
                params: method.params.clone(),
                param_types,
                return_type,
                method_bounds,
                method_kinds,
                default_body: method.default_body.clone(),
                declared_effect,
                doc: method.doc.clone(),
            });
        }

        // Convert AST associated types to AssocTypeInfo
        let associated_types = def
            .associated_types
            .iter()
            .map(|at| AssocTypeInfo {
                name: at.name.node.clone(),
                constraints: at.constraints.iter().map(|c| c.node.clone()).collect(),
                default: at.default.as_ref().map(|ann| ann.node.clone()),
            })
            .collect();
        let type_params = def
            .type_params
            .iter()
            .map(|param| TraitTypeParamInfo {
                name: param.name.node.clone(),
                kind: ast_kind_to_kind(&param.kind),
            })
            .collect();

        self.traits.insert(
            def.name.node.clone(),
            TraitInfo {
                name: def.name.node.clone(),
                type_params,
                supertraits,
                methods,
                associated_types,
                fundeps,
                definition_span: Some(def.name.span),
                doc: def.doc.clone(),
            },
        );
        self.trait_owners
            .insert(def.name.node.clone(), owner_module.to_string());
        Ok(())
    }

    /// Mark a nominal type as owned by a module for orphan-rule enforcement.
    pub fn register_trait_owner(&mut self, trait_name: &str, owner_module: &str) {
        assert!(
            owner_module.contains(':'),
            "owner tags must be tagged (e.g. pkg:, project:, repl:, kea:), got `{owner_module}`",
        );
        self.trait_owners
            .insert(trait_name.to_string(), owner_module.to_string());
    }

    /// Mark a nominal type as owned by a module for orphan-rule enforcement.
    pub fn register_type_owner(&mut self, type_name: &str, owner_module: &str) {
        assert!(
            owner_module.contains(':'),
            "owner tags must be tagged (e.g. pkg:, project:, repl:, kea:), got `{owner_module}`",
        );
        self.type_owners
            .insert(type_name.to_string(), owner_module.to_string());
    }

    /// Register a trait impl in the context of a specific module.
    ///
    /// Coherence and orphan rules:
    /// - no duplicate `(Trait, Type)` impl pairs
    /// - allowed only if the current module owns the trait OR owns the type
    pub fn register_trait_impl_in_module(
        &mut self,
        block: &kea_ast::ImplBlock,
        module_name: &str,
    ) -> Result<(), Diagnostic> {
        self.register_trait_impl_inner(block, module_name, ImplVia::Manual)
    }

    /// Register a trait impl, checking coherence.
    ///
    /// Method type-checking is done by the caller (REPL/MCP) using
    /// the same pipeline as regular function declarations.
    /// Call `add_impl_methods` afterward to record the resolved method types.
    /// If method type-checking fails, call `rollback_last_impl` to remove
    /// the incomplete entry.
    pub fn register_trait_impl(&mut self, block: &kea_ast::ImplBlock) -> Result<(), Diagnostic> {
        self.register_trait_impl_inner(block, "repl:", ImplVia::Manual)
    }

    /// Register a trait impl with explicit source metadata.
    pub fn register_trait_impl_with_via(
        &mut self,
        block: &kea_ast::ImplBlock,
        module_name: &str,
        via: ImplVia,
    ) -> Result<(), Diagnostic> {
        self.register_trait_impl_inner(block, module_name, via)
    }

    fn register_trait_impl_inner(
        &mut self,
        block: &kea_ast::ImplBlock,
        module_name: &str,
        via: ImplVia,
    ) -> Result<(), Diagnostic> {
        let trait_name = &block.trait_name;

        // Verify the trait exists
        let Some(trait_info) = self.traits.get(&trait_name.node).cloned() else {
            return Err(Diagnostic::error(
                Category::TraitBound,
                format!("trait `{}` is not defined", trait_name.node),
            )
            .at(SourceLocation {
                file_id: trait_name.span.file.0,
                start: trait_name.span.start,
                end: trait_name.span.end,
            }));
        };

        let type_params: Vec<String> = block.type_params.iter().map(|p| p.node.clone()).collect();
        let type_param_set: BTreeSet<String> = type_params.iter().cloned().collect();
        let impl_type_name = block.type_name.node.clone();

        // Extract associated type assignments and type-param trait bounds from where clause.
        let mut assoc_types = BTreeMap::new();
        let mut assoc_assignments: BTreeMap<String, TypeAnnotation> = BTreeMap::new();
        let mut param_bounds: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let declared_assoc_types: BTreeSet<String> = trait_info
            .associated_types
            .iter()
            .map(|at| at.name.clone())
            .collect();
        for item in &block.where_clause {
            match item {
                kea_ast::WhereItem::TypeAssignment { name, ty } => {
                    let is_actor_control =
                        trait_name.node == "Actor" && name.node.as_str() == "Control";
                    if !declared_assoc_types.contains(&name.node) && !is_actor_control {
                        return Err(Diagnostic::error(
                            Category::TraitBound,
                            format!(
                                "trait `{}` has no associated type `{}`",
                                trait_name.node, name.node
                            ),
                        )
                        .at(span_to_loc(name.span)));
                    }
                    if assoc_assignments.contains_key(&name.node) {
                        return Err(Diagnostic::error(
                            Category::TraitBound,
                            format!(
                                "duplicate associated type assignment `{}` in impl for `{}`",
                                name.node, trait_name.node
                            ),
                        )
                        .at(span_to_loc(name.span)));
                    }
                    validate_self_projection_targets(
                        &ty.node,
                        &declared_assoc_types,
                        ty.span,
                        "associated type assignment",
                    )?;
                    assoc_assignments.insert(name.node.clone(), ty.node.clone());
                }
                kea_ast::WhereItem::TraitBound(tb) => {
                    if self.lookup_trait(&tb.trait_name.node).is_none() {
                        return Err(Diagnostic::error(
                            Category::TraitBound,
                            format!("trait `{}` is not defined", tb.trait_name.node),
                        )
                        .at(span_to_loc(tb.trait_name.span)));
                    }
                    if type_param_set.contains(&tb.type_var.node) {
                        let bounds = param_bounds.entry(tb.type_var.node.clone()).or_default();
                        if !bounds.contains(&tb.trait_name.node) {
                            bounds.push(tb.trait_name.node.clone());
                        }
                    }
                }
            }
        }

        // Resolve explicit associated-type assignments in a fixed-point loop so
        // assignments can reference each other regardless of where-clause order.
        let mut remaining_assignments: BTreeSet<String> =
            assoc_assignments.keys().cloned().collect();
        let mut progressed = true;
        while progressed && !remaining_assignments.is_empty() {
            progressed = false;
            let pending: Vec<String> = remaining_assignments.iter().cloned().collect();
            for assoc_name in pending {
                let Some(ann) = assoc_assignments.get(&assoc_name) else {
                    continue;
                };
                if let Some(resolved) = resolve_assoc_annotation_for_impl(
                    ann,
                    &impl_type_name,
                    &type_params,
                    &assoc_types,
                ) {
                    assoc_types.insert(assoc_name.clone(), resolved);
                    remaining_assignments.remove(&assoc_name);
                    progressed = true;
                }
            }
        }
        for assoc_name in remaining_assignments {
            let ann = assoc_assignments
                .get(&assoc_name)
                .expect("remaining assignment should exist");
            // Some associated type assignments refer to nominal types that are
            // not resolvable from TraitRegistry alone at registration time.
            // Preserve their identity for coherence/lookup via a stable opaque placeholder.
            assoc_types.insert(
                assoc_name,
                Type::Opaque {
                    name: format!("__assoc_type_placeholder:{}", annotation_display(ann)),
                    params: vec![],
                },
            );
        }

        // Apply associated-type defaults in a fixed-point loop so defaults can
        // reference earlier/later associated types via projections like `Self.Item`.
        let mut progressed_defaults = true;
        while progressed_defaults {
            progressed_defaults = false;
            for assoc in &trait_info.associated_types {
                if assoc_types.contains_key(&assoc.name) {
                    continue;
                }
                let Some(default_ann) = &assoc.default else {
                    continue;
                };
                if let Some(resolved) = resolve_assoc_annotation_for_impl(
                    default_ann,
                    &impl_type_name,
                    &type_params,
                    &assoc_types,
                ) {
                    assoc_types.insert(assoc.name.clone(), resolved);
                    progressed_defaults = true;
                }
            }
        }

        for assoc in &trait_info.associated_types {
            if assoc_types.contains_key(&assoc.name) {
                continue;
            }
            if let Some(default_ann) = &assoc.default {
                // Default assignments may reference nominal types that are
                // not resolvable from TraitRegistry alone at registration time.
                // Preserve identity for coherence/lookup via a stable opaque placeholder.
                let resolved = Type::Opaque {
                    name: format!(
                        "__assoc_type_placeholder:{}",
                        annotation_display(default_ann),
                    ),
                    params: vec![],
                };
                assoc_types.insert(assoc.name.clone(), resolved);
                continue;
            }
            return Err(Diagnostic::error(
                Category::TraitBound,
                format!(
                    "missing associated type assignment `{}` in impl for trait `{}`",
                    assoc.name, trait_name.node
                ),
            )
            .at(span_to_loc(block.type_name.span)));
        }

        // Coherence: check for duplicate impls
        let type_name = &impl_type_name;
        if let Some(self_param) = trait_self_param_info(&trait_info) {
            // The dispatch trait type parameter (`Self` when present, otherwise
            // the first trait type parameter) determines the required kind for
            // the impl target constructor.
            let expected_kind = self_param.kind.clone();
            let actual_kind = infer_impl_target_kind(type_name, &type_params);
            if expected_kind != actual_kind {
                return Err(Diagnostic::error(
                    Category::TypeError,
                    format!("kind mismatch in {} implementation", trait_name.node),
                )
                .at(SourceLocation {
                    file_id: block.type_name.span.file.0,
                    start: block.type_name.span.start,
                    end: block.type_name.span.end,
                })
                .with_help(format!(
                    "{type_name} has kind {actual_kind}, but trait `{}` expects kind {}",
                    trait_name.node, expected_kind
                )));
            }
        }

        let trait_impls: Vec<&ImplInfo> = self
            .impls
            .iter()
            .filter(|i| i.trait_name == trait_name.node)
            .collect();
        let matching_impls: Vec<&ImplInfo> = trait_impls
            .iter()
            .copied()
            .filter(|i| i.type_name == *type_name)
            .collect();
        if !trait_info.fundeps.is_empty() {
            for dep in &trait_info.fundeps {
                let Some(new_from) = fundep_side_values(
                    &dep.from,
                    &trait_info,
                    type_name,
                    &type_params,
                    &assoc_types,
                ) else {
                    continue;
                };
                let Some(new_to) =
                    fundep_side_values(&dep.to, &trait_info, type_name, &type_params, &assoc_types)
                else {
                    continue;
                };

                for existing in &trait_impls {
                    let Some(existing_from) = fundep_side_values(
                        &dep.from,
                        &trait_info,
                        &existing.type_name,
                        &existing.type_params,
                        &existing.associated_types,
                    ) else {
                        continue;
                    };
                    if existing_from != new_from {
                        continue;
                    }
                    let Some(existing_to) = fundep_side_values(
                        &dep.to,
                        &trait_info,
                        &existing.type_name,
                        &existing.type_params,
                        &existing.associated_types,
                    ) else {
                        continue;
                    };
                    if existing_to != new_to {
                        return Err(Diagnostic::error(
                            Category::TraitBound,
                            format!(
                                "functional dependency conflict for `{}` in trait `{}`",
                                format_fundep(dep),
                                trait_name.node
                            ),
                        )
                        .at(span_to_loc(block.type_name.span))
                        .with_help(
                            "existing impl fixes a different dependent value for the same determining side",
                        ));
                    }
                }
            }
        }
        let new_is_parametric = !type_params.is_empty();
        if !matching_impls.is_empty() {
            let existing_parametric = matching_impls.iter().any(|i| !i.type_params.is_empty());
            if existing_parametric != new_is_parametric {
                return Err(Diagnostic::error(
                    Category::TraitBound,
                    format!(
                        "cannot mix bare and parametric impls for `{}` on `{type_name}`",
                        trait_name.node
                    ),
                )
                .at(SourceLocation {
                    file_id: block.type_name.span.file.0,
                    start: block.type_name.span.start,
                    end: block.type_name.span.end,
                }));
            }
        }

        let is_duplicate = if new_is_parametric {
            matching_impls.iter().any(|i| {
                i.type_params.len() == type_params.len() && i.associated_types == assoc_types
            })
        } else {
            let trait_has_assoc = !trait_info.associated_types.is_empty();
            matching_impls.iter().any(|i| {
                if trait_has_assoc && !assoc_types.is_empty() {
                    i.associated_types == assoc_types
                } else {
                    true
                }
            })
        };

        if is_duplicate {
            return Err(Diagnostic::error(
                Category::TraitBound,
                format!(
                    "conflicting implementation: `{}` is already implemented for `{type_name}`",
                    trait_name.node
                ),
            )
            .at(SourceLocation {
                file_id: block.type_name.span.file.0,
                start: block.type_name.span.start,
                end: block.type_name.span.end,
            }));
        }

        let trait_owner = self.trait_owners.get(&trait_name.node).map(|s| s.as_str());
        let type_owner = self.type_owners.get(type_name).map(|s| s.as_str());
        let trait_local = trait_owner.is_some_and(|o| same_ownership_scope(o, module_name));
        let type_local = type_owner.is_some_and(|o| same_ownership_scope(o, module_name));
        if type_owner.is_none() && !is_builtin_type_name(type_name) {
            return Err(Diagnostic::error(
                Category::TypeError,
                format!("type `{type_name}` is not defined"),
            )
            .at(SourceLocation {
                file_id: block.type_name.span.file.0,
                start: block.type_name.span.start,
                end: block.type_name.span.end,
            }));
        }
        if !trait_local && !type_local {
            return Err(Diagnostic::error(
                Category::TraitBound,
                format!(
                    "orphan rule violation: cannot implement foreign trait `{}` for foreign type `{}` in module `{}`",
                    trait_name.node, type_name, module_name
                ),
            )
            .at(SourceLocation {
                file_id: block.type_name.span.file.0,
                start: block.type_name.span.start,
                end: block.type_name.span.end,
            }));
        }

        // Record the impl (methods added by caller via add_impl_methods)
        self.impls.push(ImplInfo {
            trait_name: trait_name.node.clone(),
            type_name: type_name.clone(),
            type_params,
            param_bounds,
            methods: BTreeMap::new(),
            associated_types: assoc_types,
            via,
        });

        Ok(())
    }

    /// Record method types for the most recently registered trait impl.
    ///
    /// Validates that the impl provides exactly the methods the trait declares.
    /// Returns an error if methods are missing or extra.
    pub fn add_impl_methods(&mut self, methods: BTreeMap<String, Type>) -> Result<(), Diagnostic> {
        let Some(last) = self.impls.last() else {
            return Ok(());
        };
        if let Some(trait_info) = self.traits.get(&last.trait_name) {
            let expected: std::collections::BTreeSet<&str> =
                trait_info.methods.iter().map(|m| m.name.as_str()).collect();
            let required: std::collections::BTreeSet<&str> = trait_info
                .methods
                .iter()
                .filter(|m| m.default_body.is_none())
                .map(|m| m.name.as_str())
                .collect();
            let provided: std::collections::BTreeSet<&str> =
                methods.keys().map(|s| s.as_str()).collect();

            let missing: Vec<_> = required.difference(&provided).collect();
            if !missing.is_empty() && last.trait_name != "Actor" {
                return Err(Diagnostic::error(
                    Category::TraitBound,
                    format!(
                        "impl `{}` for `{}` is missing method(s): {}",
                        last.trait_name,
                        last.type_name,
                        missing
                            .iter()
                            .map(|s| format!("`{s}`"))
                            .collect::<Vec<_>>()
                            .join(", "),
                    ),
                ));
            }

            let extra: Vec<_> = if last.trait_name == "Actor" {
                Vec::new()
            } else {
                provided.difference(&expected).collect()
            };
            if !extra.is_empty() {
                return Err(Diagnostic::error(
                    Category::TraitBound,
                    format!(
                        "impl `{}` for `{}` has extra method(s) not in trait: {}",
                        last.trait_name,
                        last.type_name,
                        extra
                            .iter()
                            .map(|s| format!("`{s}`"))
                            .collect::<Vec<_>>()
                            .join(", "),
                    ),
                ));
            }
        }

        if let Some(last) = self.impls.last_mut() {
            last.methods = methods;
        }
        Ok(())
    }

    /// Remove the most recently registered trait impl.
    ///
    /// Call this when method type-checking fails after `register_trait_impl`
    /// succeeded, to avoid leaving an orphaned impl with no methods.
    pub fn rollback_last_impl(&mut self) {
        self.impls.pop();
    }

    /// Look up a trait by name.
    pub fn lookup_trait(&self, name: &str) -> Option<&TraitInfo> {
        self.traits.get(name)
    }

    /// List all registered trait names.
    pub fn all_trait_names(&self) -> impl Iterator<Item = &str> {
        self.traits.keys().map(|s| s.as_str())
    }

    fn push_unique_reason(reasons: &mut Vec<MismatchReason>, reason: MismatchReason) {
        if !reasons.contains(&reason) {
            reasons.push(reason);
        }
    }

    fn solve_constructor_goal(
        &self,
        trait_name: &str,
        ty: &Type,
        type_constructor: &str,
        type_args: &[Type],
        known_assoc: &BTreeMap<String, Type>,
    ) -> SolveOutcome {
        let Some(trait_info) = self.lookup_trait(trait_name) else {
            return SolveOutcome::NoMatch(vec![MismatchReason::UnknownTrait {
                trait_name: trait_name.to_string(),
            }]);
        };

        let mut reasons = Vec::new();
        let mut candidates = Vec::new();
        let mut saw_constructor = false;

        for (idx, imp) in self.impls.iter().enumerate() {
            if imp.trait_name != trait_name || imp.type_name != type_constructor {
                continue;
            }
            saw_constructor = true;

            let bindings: BTreeMap<String, Type> = if imp.type_params.is_empty() {
                BTreeMap::new()
            } else if imp.type_params.len() == type_args.len() {
                imp.type_params
                    .iter()
                    .cloned()
                    .zip(type_args.iter().cloned())
                    .collect()
            } else {
                Self::push_unique_reason(
                    &mut reasons,
                    MismatchReason::TypeArgArityMismatch {
                        expected: imp.type_params.len(),
                        got: type_args.len(),
                    },
                );
                continue;
            };

            let mut associated_types = BTreeMap::new();
            let mut assoc_ok = true;
            for (name, ty) in &imp.associated_types {
                associated_types.insert(
                    name.clone(),
                    instantiate_impl_type(ty, &imp.type_params, &bindings),
                );
            }
            for (assoc, expected) in known_assoc {
                let Some(found) = associated_types.get(assoc) else {
                    Self::push_unique_reason(
                        &mut reasons,
                        MismatchReason::MissingAssociatedType {
                            assoc: assoc.clone(),
                        },
                    );
                    assoc_ok = false;
                    break;
                };
                if found != expected {
                    Self::push_unique_reason(
                        &mut reasons,
                        MismatchReason::AssocTypeMismatch {
                            assoc: assoc.clone(),
                            expected: expected.clone(),
                            found: found.clone(),
                        },
                    );
                    assoc_ok = false;
                    break;
                }
            }
            if !assoc_ok {
                continue;
            }

            let mut nested_obligations = Vec::new();
            let mut bounds_ok = true;
            for (param, bound_traits) in &imp.param_bounds {
                let Some(bound_ty) = bindings.get(param) else {
                    bounds_ok = false;
                    continue;
                };
                for bound_trait in bound_traits {
                    nested_obligations.push((bound_trait.clone(), bound_ty.clone()));
                    match self.solve_goal(&TraitGoal::Implements {
                        trait_name: bound_trait.clone(),
                        ty: bound_ty.clone(),
                    }) {
                        SolveOutcome::Unique(_) => {}
                        SolveOutcome::Ambiguous(_) => {
                            Self::push_unique_reason(
                                &mut reasons,
                                MismatchReason::ParamBoundAmbiguous {
                                    param: param.clone(),
                                    bound_trait: bound_trait.clone(),
                                    ty: bound_ty.clone(),
                                },
                            );
                            bounds_ok = false;
                        }
                        SolveOutcome::NoMatch(_) => {
                            Self::push_unique_reason(
                                &mut reasons,
                                MismatchReason::ParamBoundUnsatisfied {
                                    param: param.clone(),
                                    bound_trait: bound_trait.clone(),
                                    ty: bound_ty.clone(),
                                },
                            );
                            bounds_ok = false;
                        }
                    }
                }
            }
            if !bounds_ok {
                continue;
            }

            let mut supertraits_ok = true;
            for supertrait in &trait_info.supertraits {
                match self.solve_goal(&TraitGoal::Implements {
                    trait_name: supertrait.clone(),
                    ty: ty.clone(),
                }) {
                    SolveOutcome::Unique(_) => {}
                    SolveOutcome::Ambiguous(_) => {
                        Self::push_unique_reason(
                            &mut reasons,
                            MismatchReason::SupertraitAmbiguous {
                                supertrait: supertrait.clone(),
                                ty: ty.clone(),
                            },
                        );
                        supertraits_ok = false;
                    }
                    SolveOutcome::NoMatch(_) => {
                        Self::push_unique_reason(
                            &mut reasons,
                            MismatchReason::SupertraitUnsatisfied {
                                supertrait: supertrait.clone(),
                                ty: ty.clone(),
                            },
                        );
                        supertraits_ok = false;
                    }
                }
            }
            if !supertraits_ok {
                continue;
            }

            candidates.push(SolvedCandidate {
                impl_index: Some(idx),
                trait_name: trait_name.to_string(),
                type_name: imp.type_name.clone(),
                bindings,
                associated_types,
                nested_obligations,
            });
        }

        if !saw_constructor {
            Self::push_unique_reason(
                &mut reasons,
                MismatchReason::NoImplForConstructor {
                    trait_name: trait_name.to_string(),
                    type_constructor: type_constructor.to_string(),
                },
            );
        }

        if candidates.len() > 1 && !trait_info.fundeps.is_empty() {
            let self_alias = trait_self_alias(trait_info);
            for dep in &trait_info.fundeps {
                let mut from_to: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
                for candidate in &candidates {
                    let resolve_symbol = |symbol: &str| -> Option<Type> {
                        if symbol == "Self" || self_alias == Some(symbol) {
                            return Some(ty.clone());
                        }
                        if let Some(bound) = candidate.bindings.get(symbol) {
                            return Some(bound.clone());
                        }
                        candidate.associated_types.get(symbol).cloned()
                    };
                    let Some(from_values) = dep
                        .from
                        .iter()
                        .map(|name| resolve_symbol(name))
                        .collect::<Option<Vec<_>>>()
                    else {
                        continue;
                    };
                    let Some(to_values) = dep
                        .to
                        .iter()
                        .map(|name| resolve_symbol(name))
                        .collect::<Option<Vec<_>>>()
                    else {
                        continue;
                    };
                    let from_key = from_values
                        .iter()
                        .map(std::string::ToString::to_string)
                        .collect::<Vec<_>>()
                        .join("|");
                    let to_key = to_values
                        .iter()
                        .map(std::string::ToString::to_string)
                        .collect::<Vec<_>>()
                        .join("|");
                    from_to.entry(from_key).or_default().insert(to_key);
                }

                if let Some((from_key, targets)) =
                    from_to.iter().find(|(_, targets)| targets.len() > 1)
                {
                    let from_values = from_key
                        .split('|')
                        .map(str::to_string)
                        .collect::<Vec<_>>()
                        .join(", ");
                    let target_values = targets
                        .iter()
                        .flat_map(|value| value.split('|'))
                        .map(str::to_string)
                        .collect::<Vec<_>>()
                        .join(", ");
                    Self::push_unique_reason(
                        &mut reasons,
                        MismatchReason::FundepConflict {
                            dependency: format!(
                                "{} (for [{}] implies conflicting [{}])",
                                format_fundep(dep),
                                from_values,
                                target_values
                            ),
                        },
                    );
                }
            }
            if reasons
                .iter()
                .any(|r| matches!(r, MismatchReason::FundepConflict { .. }))
            {
                return SolveOutcome::NoMatch(reasons);
            }
        }

        match candidates.len() {
            1 => SolveOutcome::Unique(candidates.remove(0)),
            0 => SolveOutcome::NoMatch(reasons),
            _ => SolveOutcome::Ambiguous(candidates),
        }
    }

    /// Solve a trait goal with explicit outcome classification.
    pub fn solve_goal(&self, goal: &TraitGoal) -> SolveOutcome {
        match goal {
            TraitGoal::Implements { trait_name, ty } => {
                if let Type::Existential { bounds, .. } = ty
                    && bounds.iter().any(|b| b == trait_name)
                {
                    return SolveOutcome::Unique(SolvedCandidate {
                        impl_index: None,
                        trait_name: trait_name.clone(),
                        type_name: "existential".to_string(),
                        bindings: BTreeMap::new(),
                        associated_types: BTreeMap::new(),
                        nested_obligations: Vec::new(),
                    });
                }

                if self.lookup_trait(trait_name).is_none() {
                    return SolveOutcome::NoMatch(vec![MismatchReason::UnknownTrait {
                        trait_name: trait_name.clone(),
                    }]);
                }

                if let Type::Constructor { name, .. } = ty {
                    if self.satisfies_recursive_by_name(
                        trait_name,
                        name,
                        &mut std::collections::BTreeSet::new(),
                    ) {
                        return SolveOutcome::Unique(SolvedCandidate {
                            impl_index: None,
                            trait_name: trait_name.clone(),
                            type_name: name.clone(),
                            bindings: BTreeMap::new(),
                            associated_types: BTreeMap::new(),
                            nested_obligations: Vec::new(),
                        });
                    }
                    return SolveOutcome::NoMatch(vec![MismatchReason::NoImplForConstructor {
                        trait_name: trait_name.clone(),
                        type_constructor: name.clone(),
                    }]);
                }

                let Some((type_constructor, type_args)) = type_constructor_for_trait(ty) else {
                    return SolveOutcome::NoMatch(vec![MismatchReason::NotATypeConstructor {
                        ty: ty.clone(),
                    }]);
                };

                self.solve_constructor_goal(
                    trait_name,
                    ty,
                    &type_constructor,
                    &type_args,
                    &BTreeMap::new(),
                )
            }
            TraitGoal::ProjectionEq {
                base_trait,
                base_ty,
                assoc,
                rhs,
            } => {
                let rhs_matches = |found: &Type| matches!(rhs, Type::Var(_)) || found == rhs;
                let outcome = self.solve_goal(&TraitGoal::Implements {
                    trait_name: base_trait.clone(),
                    ty: base_ty.clone(),
                });

                match outcome {
                    SolveOutcome::Unique(candidate) => {
                        let Some(found) = candidate.associated_types.get(assoc) else {
                            return SolveOutcome::NoMatch(vec![
                                MismatchReason::MissingAssociatedType {
                                    assoc: assoc.clone(),
                                },
                            ]);
                        };
                        if rhs_matches(found) {
                            SolveOutcome::Unique(candidate)
                        } else {
                            SolveOutcome::NoMatch(vec![MismatchReason::AssocTypeMismatch {
                                assoc: assoc.clone(),
                                expected: rhs.clone(),
                                found: found.clone(),
                            }])
                        }
                    }
                    SolveOutcome::Ambiguous(candidates) => {
                        let mut matching = Vec::new();
                        let mut reasons = Vec::new();
                        for candidate in candidates {
                            match candidate.associated_types.get(assoc) {
                                Some(found) if rhs_matches(found) => matching.push(candidate),
                                Some(found) => Self::push_unique_reason(
                                    &mut reasons,
                                    MismatchReason::AssocTypeMismatch {
                                        assoc: assoc.clone(),
                                        expected: rhs.clone(),
                                        found: found.clone(),
                                    },
                                ),
                                None => Self::push_unique_reason(
                                    &mut reasons,
                                    MismatchReason::MissingAssociatedType {
                                        assoc: assoc.clone(),
                                    },
                                ),
                            }
                        }
                        match matching.len() {
                            0 => SolveOutcome::NoMatch(reasons),
                            1 => SolveOutcome::Unique(matching.remove(0)),
                            _ => SolveOutcome::Ambiguous(matching),
                        }
                    }
                    SolveOutcome::NoMatch(reasons) => SolveOutcome::NoMatch(reasons),
                }
            }
        }
    }

    /// Find a method across all trait impls for a type.
    ///
    /// Returns:
    /// - `Ok(None)` if no matching trait method is found
    /// - `Ok(Some((trait_name, method_type)))` if exactly one trait matches
    /// - `Err(candidate_trait_names)` if multiple traits define the method
    pub fn lookup_trait_method_for_type<'a>(
        &'a self,
        type_name: &str,
        method_name: &str,
    ) -> Result<Option<(&'a str, Type)>, Vec<String>> {
        let mut found: Vec<(&str, Type)> = Vec::new();
        for imp in &self.impls {
            if imp.type_name == type_name
                && let Some(ty) = imp.methods.get(method_name)
            {
                found.push((imp.trait_name.as_str(), ty.clone()));
            }
        }

        match found.len() {
            0 => Ok(None),
            1 => Ok(Some(found[0].clone())),
            _ => Err(found
                .into_iter()
                .map(|(name, _)| name.to_string())
                .collect()),
        }
    }

    fn trait_closure_into(
        &self,
        trait_name: &str,
        seen: &mut std::collections::BTreeSet<String>,
        out: &mut Vec<String>,
    ) {
        if !seen.insert(trait_name.to_string()) {
            return;
        }
        out.push(trait_name.to_string());
        if let Some(info) = self.lookup_trait(trait_name) {
            for supertrait in &info.supertraits {
                self.trait_closure_into(supertrait, seen, out);
            }
        }
    }

    /// Return a trait and all transitive supertraits in dependency order.
    pub fn trait_closure(&self, trait_name: &str) -> Vec<String> {
        let mut seen = std::collections::BTreeSet::new();
        let mut out = Vec::new();
        self.trait_closure_into(trait_name, &mut seen, &mut out);
        out
    }

    fn satisfies_recursive_by_name(
        &self,
        trait_name: &str,
        type_name: &str,
        seen: &mut std::collections::BTreeSet<String>,
    ) -> bool {
        if !seen.insert(trait_name.to_string()) {
            return true;
        }
        if !self
            .impls
            .iter()
            .any(|i| i.trait_name == trait_name && i.type_name == type_name)
        {
            return false;
        }
        let Some(info) = self.lookup_trait(trait_name) else {
            return true;
        };
        info.supertraits
            .iter()
            .all(|supertrait| self.satisfies_recursive_by_name(supertrait, type_name, seen))
    }

    /// List all registered trait names.
    pub fn trait_names(&self) -> impl Iterator<Item = &str> {
        self.traits.keys().map(|s| s.as_str())
    }

    /// All registered traits.
    pub fn all_traits(&self) -> &BTreeMap<String, TraitInfo> {
        &self.traits
    }

    /// All trait implementations.
    pub fn all_impls(&self) -> &[ImplInfo] {
        &self.impls
    }

    /// Iterate all trait owner mappings.
    pub fn all_trait_owners(&self) -> impl Iterator<Item = (&str, &str)> {
        self.trait_owners
            .iter()
            .map(|(name, owner)| (name.as_str(), owner.as_str()))
    }

    /// Iterate all type owner mappings.
    pub fn all_type_owners(&self) -> impl Iterator<Item = (&str, &str)> {
        self.type_owners
            .iter()
            .map(|(name, owner)| (name.as_str(), owner.as_str()))
    }

    /// Which module owns this trait (for orphan rule checking).
    pub fn trait_owner(&self, name: &str) -> Option<&str> {
        self.trait_owners.get(name).map(|s| s.as_str())
    }

    /// Which module owns this type (for orphan rule checking).
    pub fn type_owner(&self, name: &str) -> Option<&str> {
        self.type_owners.get(name).map(|s| s.as_str())
    }

    /// Register an actor protocol for a type.
    ///
    /// Built from the type's `impl Actor for T` methods after they are fully
    /// type-checked and the substitution has been applied to all signatures.
    pub fn register_actor_protocol(&mut self, protocol: ActorProtocol) {
        // Replace if already exists (e.g., re-defined in REPL)
        self.actor_protocols
            .retain(|p| p.type_name != protocol.type_name);
        self.actor_protocols.push(protocol);
    }

    /// Look up the actor protocol for a type.
    pub fn find_actor_protocol(&self, type_name: &str) -> Option<&ActorProtocol> {
        self.actor_protocols
            .iter()
            .find(|p| p.type_name == type_name)
    }

    /// All registered actor protocols.
    pub fn all_actor_protocols(&self) -> &[ActorProtocol] {
        &self.actor_protocols
    }

    /// Merge a trait definition from an imported module.
    pub fn merge_trait(&mut self, name: String, info: TraitInfo) -> Result<(), String> {
        if self.traits.contains_key(&name) {
            return Err(format!("trait `{name}` is already defined"));
        }
        self.traits.insert(name, info);
        Ok(())
    }

    /// Merge a trait impl from an imported module.
    pub fn merge_impl(&mut self, info: ImplInfo) {
        // Skip if this exact impl already exists (e.g., builtin re-registration).
        let dominated = self.impls.iter().any(|existing| {
            existing.trait_name == info.trait_name
                && existing.type_name == info.type_name
                && existing.type_params.len() == info.type_params.len()
                && existing.associated_types == info.associated_types
        });
        if !dominated {
            self.impls.push(info);
        }
    }
}

fn instantiate_impl_type(
    ty: &Type,
    type_params: &[String],
    bindings: &BTreeMap<String, Type>,
) -> Type {
    fn instantiate_impl_effect_row(
        row: &EffectRow,
        type_params: &[String],
        bindings: &BTreeMap<String, Type>,
    ) -> EffectRow {
        EffectRow {
            row: RowType {
                fields: row
                    .row
                    .fields
                    .iter()
                    .map(|(label, ty)| {
                        (
                            label.clone(),
                            instantiate_impl_type(ty, type_params, bindings),
                        )
                    })
                    .collect(),
                rest: row.row.rest,
            },
        }
    }

    match ty {
        Type::Var(tv) => {
            let idx = tv.0 as usize;
            if idx < type_params.len()
                && let Some(bound) = bindings.get(&type_params[idx])
            {
                return bound.clone();
            }
            ty.clone()
        }
        Type::List(inner) => Type::List(Box::new(instantiate_impl_type(
            inner,
            type_params,
            bindings,
        ))),
        Type::FixedSizeList { element, size } => Type::FixedSizeList {
            element: Box::new(instantiate_impl_type(element, type_params, bindings)),
            size: size.clone(),
        },
        Type::Tensor { element, shape } => Type::Tensor {
            element: Box::new(instantiate_impl_type(element, type_params, bindings)),
            shape: shape.clone(),
        },
        Type::Set(inner) => Type::Set(Box::new(instantiate_impl_type(
            inner,
            type_params,
            bindings,
        ))),
        Type::Option(inner) => Type::Option(Box::new(instantiate_impl_type(
            inner,
            type_params,
            bindings,
        ))),
        Type::Map(k, v) => Type::Map(
            Box::new(instantiate_impl_type(k, type_params, bindings)),
            Box::new(instantiate_impl_type(v, type_params, bindings)),
        ),
        Type::Result(ok, err) => Type::Result(
            Box::new(instantiate_impl_type(ok, type_params, bindings)),
            Box::new(instantiate_impl_type(err, type_params, bindings)),
        ),
        Type::Existential {
            bounds,
            associated_types,
        } => Type::Existential {
            bounds: bounds.clone(),
            associated_types: associated_types
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        instantiate_impl_type(ty, type_params, bindings),
                    )
                })
                .collect(),
        },
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|t| instantiate_impl_type(t, type_params, bindings))
                .collect(),
        ),
        Type::Function(ft) => Type::Function(FunctionType {
            params: ft
                .params
                .iter()
                .map(|t| instantiate_impl_type(t, type_params, bindings))
                .collect(),
            ret: Box::new(instantiate_impl_type(&ft.ret, type_params, bindings)),
            effects: instantiate_impl_effect_row(&ft.effects, type_params, bindings),
        }),
        Type::Forall(scheme) => {
            let mut updated = (**scheme).clone();
            updated.ty = instantiate_impl_type(&updated.ty, type_params, bindings);
            Type::Forall(Box::new(updated))
        }
        Type::App(constructor, args) => Type::App(
            Box::new(instantiate_impl_type(constructor, type_params, bindings)),
            args.iter()
                .map(|arg| instantiate_impl_type(arg, type_params, bindings))
                .collect(),
        ),
        Type::Constructor {
            name,
            fixed_args,
            arity,
        } => Type::Constructor {
            name: name.clone(),
            fixed_args: fixed_args
                .iter()
                .map(|(idx, ty)| (*idx, instantiate_impl_type(ty, type_params, bindings)))
                .collect(),
            arity: *arity,
        },
        Type::Record(rt) => Type::Record(RecordType {
            name: rt.name.clone(),
            params: rt
                .params
                .iter()
                .map(|t| instantiate_impl_type(t, type_params, bindings))
                .collect(),
            row: RowType {
                fields: rt
                    .row
                    .fields
                    .iter()
                    .map(|(l, t)| (l.clone(), instantiate_impl_type(t, type_params, bindings)))
                    .collect(),
                rest: rt.row.rest,
            },
        }),
        Type::AnonRecord(row) => Type::AnonRecord(RowType {
            fields: row
                .fields
                .iter()
                .map(|(l, t)| (l.clone(), instantiate_impl_type(t, type_params, bindings)))
                .collect(),
            rest: row.rest,
        }),
        Type::Sum(st) => Type::Sum(SumType {
            name: st.name.clone(),
            type_args: st
                .type_args
                .iter()
                .map(|t| instantiate_impl_type(t, type_params, bindings))
                .collect(),
            variants: st
                .variants
                .iter()
                .map(|(vn, fields)| {
                    (
                        vn.clone(),
                        fields
                            .iter()
                            .map(|t| instantiate_impl_type(t, type_params, bindings))
                            .collect(),
                    )
                })
                .collect(),
        }),
        Type::Opaque { name, params } => Type::Opaque {
            name: name.clone(),
            params: params
                .iter()
                .map(|t| instantiate_impl_type(t, type_params, bindings))
                .collect(),
        },
        Type::Tagged { inner, tags } => Type::Tagged {
            inner: Box::new(instantiate_impl_type(inner, type_params, bindings)),
            tags: tags.clone(),
        },
        Type::Decimal { precision, scale } => Type::Decimal {
            precision: precision.clone(),
            scale: scale.clone(),
        },
        Type::Stream(inner) => Type::Stream(Box::new(instantiate_impl_type(
            inner,
            type_params,
            bindings,
        ))),
        Type::Task(inner) => Type::Task(Box::new(instantiate_impl_type(
            inner,
            type_params,
            bindings,
        ))),
        Type::Actor(inner) => Type::Actor(Box::new(instantiate_impl_type(
            inner,
            type_params,
            bindings,
        ))),
        Type::Arc(inner) => Type::Arc(Box::new(instantiate_impl_type(
            inner,
            type_params,
            bindings,
        ))),
        Type::Row(row) => Type::Row(RowType {
            fields: row
                .fields
                .iter()
                .map(|(l, t)| (l.clone(), instantiate_impl_type(t, type_params, bindings)))
                .collect(),
            rest: row.rest,
        }),
        Type::Int
        | Type::IntN(_, _)
        | Type::Float
        | Type::FloatN(_)
        | Type::Bool
        | Type::String
        | Type::Html
        | Type::Markdown
        | Type::Unit
        | Type::Atom
        | Type::Date
        | Type::DateTime
        | Type::Dynamic => ty.clone(),
    }
}

fn resolve_annotation_with_type_params(
    ann: &TypeAnnotation,
    type_param_scope: &BTreeMap<String, Type>,
    records: &RecordRegistry,
    sum_types: Option<&SumTypeRegistry>,
) -> Option<Type> {
    match ann {
        TypeAnnotation::Named(name) => type_param_scope
            .get(name)
            .cloned()
            .or_else(|| resolve_annotation(ann, records, sum_types)),
        TypeAnnotation::Applied(name, args) => {
            if let Some(constructor_ty) = type_param_scope.get(name).cloned() {
                let resolved_args: Option<Vec<_>> = args
                    .iter()
                    .map(|arg_ann| {
                        resolve_annotation_with_type_params(
                            arg_ann,
                            type_param_scope,
                            records,
                            sum_types,
                        )
                    })
                    .collect();
                return Some(Type::App(Box::new(constructor_ty), resolved_args?));
            }
            if let Some(op_ty) = eval_record_type_op(name, args, |arg_ann| {
                resolve_annotation_with_type_params(arg_ann, type_param_scope, records, sum_types)
            }) {
                return Some(op_ty);
            }
            if builtin_arity_mismatch(name, args.len()).is_some() {
                return None;
            }
            if name == "Decimal" {
                return resolve_decimal_annotation(args);
            }
            match (name.as_str(), args.as_slice()) {
                ("List", [elem]) => {
                    Some(Type::List(Box::new(resolve_annotation_with_type_params(
                        elem,
                        type_param_scope,
                        records,
                        sum_types,
                    )?)))
                }
                ("Option", [inner]) => {
                    Some(Type::Option(Box::new(resolve_annotation_with_type_params(
                        inner,
                        type_param_scope,
                        records,
                        sum_types,
                    )?)))
                }
                ("Result", [ok, err]) => Some(Type::Result(
                    Box::new(resolve_annotation_with_type_params(
                        ok,
                        type_param_scope,
                        records,
                        sum_types,
                    )?),
                    Box::new(resolve_annotation_with_type_params(
                        err,
                        type_param_scope,
                        records,
                        sum_types,
                    )?),
                )),
                ("Map", [key, val]) => Some(Type::Map(
                    Box::new(resolve_annotation_with_type_params(
                        key,
                        type_param_scope,
                        records,
                        sum_types,
                    )?),
                    Box::new(resolve_annotation_with_type_params(
                        val,
                        type_param_scope,
                        records,
                        sum_types,
                    )?),
                )),
                ("Set", [elem]) => Some(Type::Set(Box::new(resolve_annotation_with_type_params(
                    elem,
                    type_param_scope,
                    records,
                    sum_types,
                )?))),
                ("Actor", [inner]) => {
                    Some(Type::Actor(Box::new(resolve_annotation_with_type_params(
                        inner,
                        type_param_scope,
                        records,
                        sum_types,
                    )?)))
                }
                ("Arc", [inner]) => Some(Type::Arc(Box::new(resolve_annotation_with_type_params(
                    inner,
                    type_param_scope,
                    records,
                    sum_types,
                )?))),
                ("Stream", [inner]) => {
                    Some(Type::Stream(Box::new(resolve_annotation_with_type_params(
                        inner,
                        type_param_scope,
                        records,
                        sum_types,
                    )?)))
                }
                ("Task", [inner]) => {
                    Some(Type::Task(Box::new(resolve_annotation_with_type_params(
                        inner,
                        type_param_scope,
                        records,
                        sum_types,
                    )?)))
                }
                ("Tagged", [inner]) => Some(Type::Tagged {
                    inner: Box::new(resolve_annotation_with_type_params(
                        inner,
                        type_param_scope,
                        records,
                        sum_types,
                    )?),
                    tags: BTreeMap::new(),
                }),
                _ => resolve_named_type_application(name, args, records, sum_types, |arg_ann| {
                    resolve_annotation_with_type_params(
                        arg_ann,
                        type_param_scope,
                        records,
                        sum_types,
                    )
                }),
            }
        }
        TypeAnnotation::Row { fields, rest } => row_annotation_to_type_with(
            fields,
            rest,
            |field_ann| {
                resolve_annotation_with_type_params(field_ann, type_param_scope, records, sum_types)
            },
        ),
        TypeAnnotation::EffectRow(_) => None,
        TypeAnnotation::Tuple(elems) => {
            let types: Option<Vec<_>> = elems
                .iter()
                .map(|e| {
                    resolve_annotation_with_type_params(e, type_param_scope, records, sum_types)
                })
                .collect();
            Some(Type::Tuple(types?))
        }
        TypeAnnotation::Forall { type_vars, ty } => {
            let mut scoped = type_param_scope.clone();
            let mut used: BTreeSet<TypeVarId> = scoped
                .values()
                .filter_map(|ty| match ty {
                    Type::Var(tv) => Some(*tv),
                    _ => None,
                })
                .collect();
            let mut next_placeholder = u32::MAX;
            let mut quantified = Vec::new();
            let mut kinds = BTreeMap::new();
            for name in type_vars {
                let mut candidate = TypeVarId(next_placeholder);
                while used.contains(&candidate) {
                    next_placeholder = next_placeholder.wrapping_sub(1);
                    candidate = TypeVarId(next_placeholder);
                }
                next_placeholder = next_placeholder.wrapping_sub(1);
                scoped.insert(name.clone(), Type::Var(candidate));
                used.insert(candidate);
                quantified.push(candidate);
                kinds.insert(candidate, Kind::Star);
            }
            Some(Type::Forall(Box::new(TypeScheme {
                type_vars: quantified,
                row_vars: Vec::new(),
                dim_vars: vec![],
                lacks: BTreeMap::new(),
                bounds: BTreeMap::new(),
                kinds,
                ty: resolve_annotation_with_type_params(ty, &scoped, records, sum_types)?,
            })))
        }
        TypeAnnotation::Function(params, ret) => {
            let param_types: Option<Vec<_>> = params
                .iter()
                .map(|p| {
                    resolve_annotation_with_type_params(p, type_param_scope, records, sum_types)
                })
                .collect();
            Some(Type::Function(FunctionType {
                params: param_types?,
                ret: Box::new(resolve_annotation_with_type_params(
                    ret,
                    type_param_scope,
                    records,
                    sum_types,
                )?),
                effects: EffectRow::pure(),
            }))
        }
        TypeAnnotation::FunctionWithEffect(params, effect, ret) => {
            let param_types: Option<Vec<_>> = params
                .iter()
                .map(|p| {
                    resolve_annotation_with_type_params(p, type_param_scope, records, sum_types)
                })
                .collect();
            let mut effect_var_bindings = BTreeMap::new();
            let mut next_effect_var = 0u32;
            let effects = function_param_effect_row_from_type_annotation(
                ann,
                &mut effect_var_bindings,
                &mut next_effect_var,
            )
            .or_else(|| effect_annotation_to_compat_row(&effect.node, Some(records)))
            .unwrap_or_else(pure_effect_row);
            Some(Type::Function(FunctionType {
                params: param_types?,
                ret: Box::new(resolve_annotation_with_type_params(
                    ret,
                    type_param_scope,
                    records,
                    sum_types,
                )?),
                effects,
            }))
        }
        TypeAnnotation::Optional(inner) => Some(Type::Option(Box::new(
            resolve_annotation_with_type_params(inner, type_param_scope, records, sum_types)?,
        ))),
        TypeAnnotation::Existential {
            bounds,
            associated_types,
        } => {
            let resolved_assoc: Option<BTreeMap<String, Type>> = associated_types
                .iter()
                .map(|(name, ann)| {
                    resolve_annotation_with_type_params(ann, type_param_scope, records, sum_types)
                        .map(|ty| (name.clone(), ty))
                })
                .collect();
            Some(Type::Existential {
                bounds: bounds.clone(),
                associated_types: resolved_assoc?,
            })
        }
        TypeAnnotation::Projection { .. } | TypeAnnotation::DimLiteral(_) => None,
    }
}

fn is_builtin_type_name(name: &str) -> bool {
    matches!(
        name,
        "Int"
            | "Int8"
            | "Int16"
            | "Int32"
            | "Int64"
            | "UInt8"
            | "UInt16"
            | "UInt32"
            | "UInt64"
            | "Float"
            | "Float16"
            | "Float32"
            | "Float64"
            | "Decimal"
            | "Bool"
            | "String"
            | "Unit"
            | "Dynamic"
            | "Option"
            | "Result"
            | "List"
            | "Map"
            | "Set"
            | "Actor"
            | "Stream"
            | "Task"
            | "Connection"
            | "IOError"
            | "SchemaError"
            | "ExecError"
            | "ActorError"
            | "Date"
            | "DateTime"
            | "Html"
            | "Markdown"
            | "Arc"
            | "Atom"
            | "Validated"
            | "Step"
            | "Seq"
    )
}

/// Extract the ownership scope from a tagged ownership string.
///
/// Ownership strings encode which package/project a type or trait belongs to:
/// - `"project:Foo.Bar"` → `"project"` (all project modules share one scope)
/// - `"pkg:my_lib"` → `"pkg:my_lib"` (per-package scope)
/// - `"kea:"` → `"kea"` (stdlib singleton)
/// - `"repl:"` → `"repl"` (REPL singleton)
///
/// Internal owners should always be tagged; unrecognized/untagged values
/// are treated as exact-match scopes for defensive handling.
pub(crate) fn ownership_scope(s: &str) -> &str {
    if let Some((prefix, _rest)) = s.split_once(':') {
        match prefix {
            "project" | "repl" | "kea" => prefix,
            "pkg" => s,
            _ => s,
        }
    } else {
        s
    }
}

/// Check if two ownership strings are in the same package/project scope.
pub(crate) fn same_ownership_scope(a: &str, b: &str) -> bool {
    ownership_scope(a) == ownership_scope(b)
}

fn looks_like_type_var_name(name: &str) -> bool {
    name.chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_lowercase())
        && !is_builtin_type_name(name)
}

impl Default for TraitRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Generalization and instantiation
// ---------------------------------------------------------------------------

/// Generalize a type into a type scheme by quantifying over variables
/// that are free in the type but not free in the environment.
///
/// This is the core of let-polymorphism: `let id = |x| x` gets
/// generalized to `forall a. a -> a` because `a` is free in `a -> a`
/// but not in the environment.
///
/// Lacks constraints on quantified row variables are preserved in
/// the scheme so they transfer to fresh variables during instantiation.
pub fn generalize(
    ty: &Type,
    env: &TypeEnv,
    subst: &Substitution,
    lacks: &crate::LacksConstraints,
    trait_bounds: &BTreeMap<TypeVarId, BTreeSet<String>>,
    type_var_kinds: &BTreeMap<TypeVarId, Kind>,
) -> TypeScheme {
    // Apply current substitution to get the most resolved type.
    let ty = subst.apply(ty);

    // Find variables free in the type but not in the environment.
    // We need to apply subst to env types too for consistency.
    let env_type_vars = env_free_type_vars(env, subst);
    let env_row_vars = env_free_row_vars(env, subst);
    let env_dim_vars = env_free_dim_vars(env, subst);

    let ty_type_vars = free_type_vars(&ty);
    let ty_row_vars = free_row_vars(&ty);
    let ty_dim_vars = free_dim_vars(&ty);

    let gen_type_vars: Vec<TypeVarId> = ty_type_vars.difference(&env_type_vars).copied().collect();
    let gen_row_vars: Vec<RowVarId> = ty_row_vars.difference(&env_row_vars).copied().collect();
    let gen_dim_vars: Vec<_> = ty_dim_vars.difference(&env_dim_vars).copied().collect();

    // Preserve lacks constraints for quantified row vars.
    let mut scheme_lacks = BTreeMap::new();
    for &rv in &gen_row_vars {
        if let Some(labels) = lacks.get(rv) {
            scheme_lacks.insert(rv, labels.clone());
        }
    }

    // Preserve trait bounds for quantified type vars.
    let mut scheme_bounds = BTreeMap::new();
    for &tv in &gen_type_vars {
        if let Some(traits) = trait_bounds.get(&tv)
            && !traits.is_empty()
        {
            scheme_bounds.insert(tv, traits.clone());
        }
    }

    // Preserve explicit kind assignments for quantified type vars.
    let mut scheme_kinds = BTreeMap::new();
    for &tv in &gen_type_vars {
        if let Some(kind) = type_var_kinds.get(&tv) {
            scheme_kinds.insert(tv, kind.clone());
        }
    }

    TypeScheme {
        type_vars: gen_type_vars,
        row_vars: gen_row_vars,
        dim_vars: gen_dim_vars,
        lacks: scheme_lacks,
        bounds: scheme_bounds,
        kinds: scheme_kinds,
        ty,
    }
}

/// Collect free type vars from environment, applying substitution first.
fn env_free_type_vars(env: &TypeEnv, subst: &Substitution) -> BTreeSet<TypeVarId> {
    let mut vars = BTreeSet::new();
    for scope in &env.bindings {
        for scheme in scope.values() {
            let resolved = subst.apply(&scheme.ty);
            let body_vars = free_type_vars(&resolved);
            let quantified: BTreeSet<_> = scheme.type_vars.iter().copied().collect();
            vars.extend(body_vars.difference(&quantified));
        }
    }
    vars
}

/// Collect free row vars from environment, applying substitution first.
fn env_free_row_vars(env: &TypeEnv, subst: &Substitution) -> BTreeSet<RowVarId> {
    let mut vars = BTreeSet::new();
    for scope in &env.bindings {
        for scheme in scope.values() {
            let resolved = subst.apply(&scheme.ty);
            let body_vars = free_row_vars(&resolved);
            let quantified: BTreeSet<_> = scheme.row_vars.iter().copied().collect();
            vars.extend(body_vars.difference(&quantified));
        }
    }
    vars
}

/// Collect free dim vars from environment, applying substitution first.
fn env_free_dim_vars(env: &TypeEnv, subst: &Substitution) -> BTreeSet<DimVarId> {
    let mut vars = BTreeSet::new();
    for scope in &env.bindings {
        for scheme in scope.values() {
            let resolved = subst.apply(&scheme.ty);
            let body_vars = free_dim_vars(&resolved);
            let quantified: BTreeSet<_> = scheme.dim_vars.iter().copied().collect();
            vars.extend(body_vars.difference(&quantified));
        }
    }
    vars
}

/// Instantiate a type scheme by replacing quantified variables with
/// fresh ones. Transfers lacks constraints to the fresh row variables.
pub fn instantiate_with_span(scheme: &TypeScheme, unifier: &mut Unifier, span: Span) -> Type {
    if scheme.is_mono() {
        return scheme.ty.clone();
    }

    // Create fresh variables for each quantified variable.
    let mut type_mapping = BTreeMap::new();
    for &tv in &scheme.type_vars {
        let fresh = if let Some(kind) = scheme.kinds.get(&tv) {
            unifier.fresh_type_var_with_kind(kind.clone())
        } else {
            unifier.fresh_type_var()
        };
        type_mapping.insert(tv, fresh);
    }

    let mut row_mapping = BTreeMap::new();
    for &rv in &scheme.row_vars {
        row_mapping.insert(rv, unifier.fresh_row_var());
    }
    let mut dim_mapping = BTreeMap::new();
    for &dv in &scheme.dim_vars {
        dim_mapping.insert(dv, unifier.fresh_dim_var());
    }

    // Transfer lacks constraints to fresh row variables.
    for (&old_rv, labels) in &scheme.lacks {
        if let Some(&new_rv) = row_mapping.get(&old_rv) {
            for label in labels {
                let prov = Provenance {
                    span,
                    reason: Reason::RowExtension {
                        label: label.clone(),
                    },
                };
                constrain_lacks(unifier, new_rv, label.clone(), &prov);
            }
        }
    }

    // Transfer trait bounds to fresh type variables.
    for (&old_tv, traits) in &scheme.bounds {
        if let Some(&new_tv) = type_mapping.get(&old_tv) {
            for trait_name in traits {
                let prov = Provenance {
                    span,
                    reason: Reason::TraitBound {
                        trait_name: trait_name.clone(),
                    },
                };
                constrain_trait_obligation(unifier, &Type::Var(new_tv), trait_name, &prov);
            }
        }
    }

    // Apply the mapping to the type.
    rename_type(&scheme.ty, &type_mapping, &row_mapping, &dim_mapping)
}

/// Instantiate a type scheme for non-source-driven contexts.
pub fn instantiate(scheme: &TypeScheme, unifier: &mut Unifier) -> Type {
    instantiate_with_span(scheme, unifier, Span::synthetic())
}

/// Seed annotation-time type-parameter scope from `fn ... where ...` bounds.
///
/// Bounds whose left side matches a function parameter name keep the existing
/// behavior (`where x: Trait` constrains parameter `x`) and are intentionally
/// skipped here. Non-parameter bounds (for example `where F: Applicative`)
/// introduce named type parameters usable in annotations like `F(a)`.
pub(crate) fn seed_fn_where_type_params(
    fn_decl: &kea_ast::FnDecl,
    traits: &TraitRegistry,
    unifier: &mut Unifier,
) {
    if fn_decl.where_clause.is_empty() {
        return;
    }

    let param_names: BTreeSet<String> = fn_decl
        .params
        .iter()
        .filter_map(|p| p.name().map(|n| n.to_string()))
        .collect();
    let mut scope = unifier.annotation_type_param_scope.clone();

    for bound in &fn_decl.where_clause {
        let var_name = &bound.type_var.node;
        if param_names.contains(var_name) {
            continue;
        }

        let expected_kind = match where_trait_bound_kind(
            traits,
            &bound.type_var,
            &bound.trait_name,
            "function where clauses",
        ) {
            Ok(kind) => kind,
            Err(diag) => {
                unifier.push_error(diag);
                continue;
            }
        };

        let tv = match scope.get(var_name) {
            Some(Type::Var(existing_tv)) => {
                if let Some(existing_kind) = unifier.type_var_kinds.get(existing_tv) {
                    let existing_kind = existing_kind.clone();
                    let prov = Provenance {
                        span: bound.type_var.span,
                        reason: Reason::TraitBound {
                            trait_name: bound.trait_name.node.clone(),
                        },
                    };
                    constrain_kind_eq(unifier, &existing_kind, &expected_kind, &prov);
                }
                *existing_tv
            }
            _ => {
                let fresh = unifier.fresh_type_var_with_kind(expected_kind.clone());
                scope.insert(var_name.clone(), Type::Var(fresh));
                fresh
            }
        };

        let prov = Provenance {
            span: bound.type_var.span,
            reason: Reason::TraitBound {
                trait_name: bound.trait_name.node.clone(),
            },
        };
        constrain_trait_obligation(unifier, &Type::Var(tv), &bound.trait_name.node, &prov);
    }

    if !scope.is_empty() {
        unifier.set_annotation_type_param_scope(scope);
    }
}

/// Context-first wrapper for seeding `fn ... where` bounds.
///
/// Keeps call sites on the `InferenceContext` API surface.
pub fn seed_fn_where_type_params_in_context(
    fn_decl: &kea_ast::FnDecl,
    traits: &TraitRegistry,
    ctx: &mut InferenceContext,
) {
    seed_fn_where_type_params(fn_decl, traits, ctx);
}

/// Apply where-clause bounds from a FnDecl to a generalized TypeScheme.
///
/// Maps parameter names in the where-clause to their positions in the
/// function type, then records trait bounds on the corresponding quantified
/// type variables.
///
/// Example: `fn total(x) where x: Additive { x }`
/// - param "x" is at position 0
/// - scheme.ty is `(t0) -> t0` with type_vars = [t0]
/// - After: scheme.bounds = {t0: {"Additive"}}
pub fn apply_where_clause(
    scheme: &mut TypeScheme,
    fn_decl: &kea_ast::FnDecl,
    subst: &Substitution,
) {
    if fn_decl.where_clause.is_empty() {
        return;
    }

    // Get parameter names.
    let param_names: Vec<String> = fn_decl
        .params
        .iter()
        .map(|p| p.name().unwrap_or("_").to_string())
        .collect();

    // Get the function type from the scheme.
    let Type::Function(ref ft) = scheme.ty else {
        return;
    };

    let quantified: BTreeSet<TypeVarId> = scheme.type_vars.iter().copied().collect();

    for bound in &fn_decl.where_clause {
        // Find the parameter position for this bound's type variable name.
        let Some(idx) = param_names.iter().position(|p| p == &bound.type_var.node) else {
            continue;
        };
        if idx >= ft.params.len() {
            continue;
        }

        // Resolve the param type to see if it's a quantified type var.
        let param_ty = subst.apply(&ft.params[idx]);
        if let Type::Var(tv) = param_ty
            && quantified.contains(&tv)
        {
            scheme
                .bounds
                .entry(tv)
                .or_default()
                .insert(bound.trait_name.node.clone());
        }
    }
}

fn is_infer_placeholder_annotation(ann: &TypeAnnotation) -> bool {
    matches!(ann, TypeAnnotation::Named(name) if name == "_")
}

fn has_concrete_return_annotation(ann: &Option<kea_ast::Spanned<TypeAnnotation>>) -> bool {
    ann.as_ref()
        .is_some_and(|ann| !is_infer_placeholder_annotation(&ann.node))
}

fn missing_param_annotation_diagnostic(owner_span: Span, missing: &[(String, Span)]) -> Diagnostic {
    let mut diag = if missing.len() == 1 {
        Diagnostic::error(Category::MissingAnnotation, "missing type annotation on parameter")
    } else {
        Diagnostic::error(
            Category::MissingAnnotation,
            "missing type annotations on parameters",
        )
    }
    .at(span_to_loc(owner_span))
    .with_help(
        "named functions require type annotations on all parameters.\nclosures and let bindings can still infer types.",
    );

    for (name, span) in missing {
        diag = diag.with_label(
            span_to_loc(*span),
            format!("parameter `{name}` requires a type annotation"),
        );
    }

    diag
}

fn collect_missing_param_annotations(
    params: &[kea_ast::Param],
    allow_self_without_annotation: bool,
) -> Vec<(String, Span)> {
    params
        .iter()
        .filter_map(|param| {
            if allow_self_without_annotation && param.name() == Some("self") {
                return None;
            }
            if param.annotation.is_none() {
                return Some((param.name().unwrap_or("_").to_string(), param.pattern.span));
            }
            None
        })
        .collect()
}

/// Validate required type annotations on a named `fn` declaration.
///
/// Rules:
/// - all parameters require annotations (`_` is allowed for explicit inference)
/// - public functions require a non-`_` return annotation
pub fn validate_fn_decl_annotations(fn_decl: &kea_ast::FnDecl) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let missing = collect_missing_param_annotations(&fn_decl.params, false);
    if !missing.is_empty() {
        diagnostics.push(missing_param_annotation_diagnostic(fn_decl.span, &missing));
    }
    if fn_decl.public && !has_concrete_return_annotation(&fn_decl.return_annotation) {
        diagnostics.push(
            Diagnostic::error(
                Category::MissingAnnotation,
                "public function missing return type",
            )
            .at(span_to_loc(fn_decl.name.span))
            .with_label(
                span_to_loc(fn_decl.name.span),
                format!(
                    "public function `{}` requires a return type annotation",
                    fn_decl.name.node
                ),
            )
            .with_help(
                "public functions require return type annotations because they define your module API.",
            ),
        );
    }
    diagnostics
}

/// Validate required type annotations on a named `expr` declaration.
///
/// Rules match regular function declarations.
pub fn validate_expr_decl_annotations(expr_decl: &kea_ast::ExprDecl) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let missing = collect_missing_param_annotations(&expr_decl.params, false);
    if !missing.is_empty() {
        diagnostics.push(missing_param_annotation_diagnostic(
            expr_decl.span,
            &missing,
        ));
    }
    if expr_decl.public && !has_concrete_return_annotation(&expr_decl.return_annotation) {
        diagnostics.push(
            Diagnostic::error(
                Category::MissingAnnotation,
                "public function missing return type",
            )
            .at(span_to_loc(expr_decl.name.span))
            .with_label(
                span_to_loc(expr_decl.name.span),
                format!(
                    "public function `{}` requires a return type annotation",
                    expr_decl.name.node
                ),
            )
            .with_help(
                "public functions require return type annotations because they define your module API.",
            ),
        );
    }
    diagnostics
}

/// Validate required type annotations on a trait method.
///
/// Rules:
/// - all non-`self` parameters require annotations
/// - return annotation is required and cannot be `_`
pub fn validate_trait_method_annotations(
    trait_name: &str,
    method: &kea_ast::TraitMethod,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let missing = collect_missing_param_annotations(&method.params, true);
    if !missing.is_empty() {
        diagnostics.push(missing_param_annotation_diagnostic(method.span, &missing));
    }
    if !has_concrete_return_annotation(&method.return_annotation) {
        diagnostics.push(
            Diagnostic::error(
                Category::MissingAnnotation,
                "trait method missing return type",
            )
            .at(span_to_loc(method.name.span))
            .with_label(
                span_to_loc(method.name.span),
                format!(
                    "trait method `{}.{}` requires a return type annotation",
                    trait_name, method.name.node
                ),
            ),
        );
    }
    diagnostics
}

/// Validate required type annotations on an impl method.
///
/// Rules:
/// - all non-`self` parameters require annotations
/// - return annotation is optional
pub fn validate_impl_method_annotations(method: &kea_ast::FnDecl) -> Vec<Diagnostic> {
    let missing = collect_missing_param_annotations(&method.params, true);
    let mut diagnostics = Vec::new();
    if !missing.is_empty() {
        diagnostics.push(missing_param_annotation_diagnostic(method.span, &missing));
    }
    diagnostics
}

fn legacy_effect_annotation_diagnostic(
    effect_ann: &kea_ast::Spanned<kea_ast::EffectAnnotation>,
    context: &str,
) -> Option<Diagnostic> {
    let (legacy, replacement) = match effect_ann.node {
        kea_ast::EffectAnnotation::Volatile => ("volatile", "-[Volatile]>"),
        kea_ast::EffectAnnotation::Impure => ("impure", "-[IO]>"),
        _ => return None,
    };
    Some(
        Diagnostic::warning(
            Category::TypeError,
            format!(
                "legacy `{legacy}` effect syntax is deprecated on {context}; use row syntax"
            ),
        )
        .at(span_to_loc(effect_ann.span))
        .with_help(format!(
            "replace with `{replacement}` (or another explicit row) and use `->` for pure functions"
        )),
    )
}

/// Validate declaration-level function annotations in a parsed module.
///
/// Covers:
/// - `fn` and `expr` declarations
/// - trait methods
/// - impl methods
pub fn validate_module_fn_annotations(module: &kea_ast::Module) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for decl in &module.declarations {
        match &decl.node {
            kea_ast::DeclKind::Function(fn_decl) => {
                diagnostics.extend(validate_fn_decl_annotations(fn_decl));
                if let Some(effect_ann) = &fn_decl.effect_annotation
                    && let Some(diag) =
                        legacy_effect_annotation_diagnostic(effect_ann, "function declaration")
                {
                    diagnostics.push(diag);
                }
            }
            kea_ast::DeclKind::ExprFn(expr_decl) => {
                diagnostics.extend(validate_expr_decl_annotations(expr_decl));
                if let Some(effect_ann) = &expr_decl.effect_annotation
                    && let Some(diag) =
                        legacy_effect_annotation_diagnostic(effect_ann, "expr declaration")
                {
                    diagnostics.push(diag);
                }
            }
            kea_ast::DeclKind::TraitDef(def) => {
                for method in &def.methods {
                    diagnostics.extend(validate_trait_method_annotations(&def.name.node, method));
                    if let Some(effect_ann) = &method.effect_annotation
                        && let Some(diag) =
                            legacy_effect_annotation_diagnostic(effect_ann, "trait method")
                    {
                        diagnostics.push(diag);
                    }
                }
            }
            kea_ast::DeclKind::ImplBlock(ib) => {
                for method in &ib.methods {
                    diagnostics.extend(validate_impl_method_annotations(method));
                    if let Some(effect_ann) = &method.effect_annotation
                        && let Some(diag) =
                            legacy_effect_annotation_diagnostic(effect_ann, "impl method")
                    {
                        diagnostics.push(diag);
                    }
                }
            }
            _ => {}
        }
    }
    diagnostics
}

#[derive(Clone, Copy)]
enum AnnotationTargetKind {
    Function,
    ExprFunction,
    Record,
    RecordField,
    TypeDef,
    TypeVariant,
    VariantField,
}

impl AnnotationTargetKind {
    fn label(self) -> &'static str {
        match self {
            AnnotationTargetKind::Function => "function declaration",
            AnnotationTargetKind::ExprFunction => "expr declaration",
            AnnotationTargetKind::Record => "record declaration",
            AnnotationTargetKind::RecordField => "record field",
            AnnotationTargetKind::TypeDef => "type declaration",
            AnnotationTargetKind::TypeVariant => "type variant",
            AnnotationTargetKind::VariantField => "variant field",
        }
    }
}

fn annotation_name_known(name: &str) -> bool {
    matches!(
        name,
        "rename" | "default" | "skip_if" | "tagged" | "deprecated"
    )
}

fn annotation_name_suggestion(name: &str) -> Option<&'static str> {
    const KNOWN: [&str; 5] = ["rename", "default", "skip_if", "tagged", "deprecated"];
    let mut best: Option<(&str, usize)> = None;
    for candidate in KNOWN {
        let dist = edit_distance(name, candidate);
        if best.is_none_or(|(_, current)| dist < current) {
            best = Some((candidate, dist));
        }
    }
    match best {
        Some((candidate, dist)) if dist <= 3 => Some(candidate),
        _ => None,
    }
}

fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut curr = vec![0; b.len() + 1];

    for (i, ca) in a.iter().enumerate() {
        curr[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let cost = usize::from(ca != cb);
            curr[j + 1] = (prev[j + 1] + 1).min(curr[j] + 1).min(prev[j] + cost);
        }
        std::mem::swap(&mut prev, &mut curr);
    }

    prev[b.len()]
}

fn annotation_is_serialization(name: &str) -> bool {
    matches!(name, "rename" | "default" | "skip_if" | "tagged")
}

fn has_serialize_derive(derives: &[kea_ast::Spanned<String>]) -> bool {
    derives.iter().any(|d| d.node == "Serialize")
}

fn is_string_literal_expr(expr: &Expr) -> bool {
    matches!(expr.node, ExprKind::Lit(Lit::String(_)))
}

fn is_atom_literal_expr(expr: &Expr) -> bool {
    matches!(expr.node, ExprKind::Atom(_))
}

fn is_optional_annotation(ann: &kea_ast::TypeAnnotation) -> bool {
    matches!(ann, kea_ast::TypeAnnotation::Optional(_))
}

fn is_option_is_none_reference(expr: &Expr) -> bool {
    match &expr.node {
        ExprKind::FieldAccess { expr, field, .. } => {
            matches!(&expr.node, ExprKind::Var(module) if module == "Option")
                && field.node == "is_none"
        }
        _ => false,
    }
}

fn is_annotation_expr_pure(expr: &Expr) -> bool {
    match &expr.node {
        ExprKind::Lit(_) | ExprKind::None | ExprKind::Atom(_) | ExprKind::Var(_) => true,
        ExprKind::Tuple(items) | ExprKind::List(items) | ExprKind::Block(items) => {
            items.iter().all(is_annotation_expr_pure)
        }
        ExprKind::StringInterp(parts) => parts.iter().all(|p| match p {
            kea_ast::StringInterpPart::Literal(_) => true,
            kea_ast::StringInterpPart::Expr(e) => is_annotation_expr_pure(e),
        }),
        ExprKind::UnaryOp { operand, .. } => is_annotation_expr_pure(operand),
        ExprKind::BinaryOp { left, right, .. } => {
            is_annotation_expr_pure(left) && is_annotation_expr_pure(right)
        }
        ExprKind::Range { start, end, .. } => {
            is_annotation_expr_pure(start) && is_annotation_expr_pure(end)
        }
        ExprKind::FieldAccess { expr, .. } => is_annotation_expr_pure(expr),
        ExprKind::As { expr, .. } => is_annotation_expr_pure(expr),
        ExprKind::Await { expr, .. } => is_annotation_expr_pure(expr),
        ExprKind::Constructor { args, .. } => {
            args.iter().all(|a| is_annotation_expr_pure(&a.value))
        }
        ExprKind::Record { fields, spread, .. } => {
            fields.iter().all(|(_, v)| is_annotation_expr_pure(v))
                && spread.as_ref().is_none_or(|e| is_annotation_expr_pure(e))
        }
        ExprKind::AnonRecord { fields, spread } => {
            fields.iter().all(|(_, v)| is_annotation_expr_pure(v))
                && spread.as_ref().is_none_or(|e| is_annotation_expr_pure(e))
        }
        ExprKind::MapLiteral(entries) => entries
            .iter()
            .all(|(k, v)| is_annotation_expr_pure(k) && is_annotation_expr_pure(v)),
        _ => false,
    }
}

fn first_positional_arg(args: &[kea_ast::Argument]) -> Option<&Expr> {
    args.iter().find(|a| a.label.is_none()).map(|a| &a.value)
}

fn named_arg<'a>(args: &'a [kea_ast::Argument], name: &str) -> Option<&'a Expr> {
    args.iter()
        .find(|a| a.label.as_ref().map(|l| l.node.as_str()) == Some(name))
        .map(|a| &a.value)
}

fn literal_matches_type_annotation(expr: &Expr, ann: &kea_ast::TypeAnnotation) -> Option<bool> {
    match (&expr.node, ann) {
        (ExprKind::Lit(Lit::Int(_)), kea_ast::TypeAnnotation::Named(name)) => Some(matches!(
            name.as_str(),
            "Int" | "Int8" | "Int16" | "Int32" | "Int64" | "UInt8" | "UInt16" | "UInt32" | "UInt64"
        )),
        (ExprKind::Lit(Lit::Float(_)), kea_ast::TypeAnnotation::Named(name)) => Some(matches!(
            name.as_str(),
            "Float" | "Float16" | "Float32" | "Float64"
        )),
        (ExprKind::Lit(Lit::String(_)), kea_ast::TypeAnnotation::Named(name)) => {
            Some(name == "String")
        }
        (ExprKind::Lit(Lit::Bool(_)), kea_ast::TypeAnnotation::Named(name)) => {
            Some(name == "Bool")
        }
        (ExprKind::None, kea_ast::TypeAnnotation::Optional(_)) => Some(true),
        _ => None,
    }
}

fn validate_annotation_arguments(
    ann: &kea_ast::Annotation,
    target: AnnotationTargetKind,
    field_ty: Option<&kea_ast::TypeAnnotation>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let name = ann.name.node.as_str();
    if !annotation_name_known(name) {
        let suggestion = annotation_name_suggestion(name)
            .map(|candidate| format!(" Did you mean `@{candidate}`?"))
            .unwrap_or_default();
        diagnostics.push(
            Diagnostic::error(
                Category::TypeError,
                format!("unknown annotation `@{name}`.{suggestion}"),
            )
            .at(span_to_loc(ann.span)),
        );
        return diagnostics;
    }

    for arg in &ann.args {
        if !is_annotation_expr_pure(&arg.value) {
            diagnostics.push(
                Diagnostic::error(
                    Category::TypeError,
                    "annotation arguments must be pure expressions",
                )
                .at(span_to_loc(arg.value.span)),
            );
        }
    }

    match name {
        "rename" => {
            if !matches!(
                target,
                AnnotationTargetKind::RecordField
                    | AnnotationTargetKind::TypeVariant
                    | AnnotationTargetKind::VariantField
            ) {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!("`@rename` is not valid on {}", target.label()),
                    )
                    .at(span_to_loc(ann.span)),
                );
            }
            if ann.args.len() != 1 || ann.args[0].label.is_some() {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`@rename` expects exactly one positional string argument",
                    )
                    .at(span_to_loc(ann.span)),
                );
            } else if !is_string_literal_expr(&ann.args[0].value) {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`@rename` argument must be a string literal",
                    )
                    .at(span_to_loc(ann.args[0].value.span)),
                );
            }
        }
        "default" => {
            if !matches!(
                target,
                AnnotationTargetKind::RecordField | AnnotationTargetKind::VariantField
            ) {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!("`@default` is not valid on {}", target.label()),
                    )
                    .at(span_to_loc(ann.span)),
                );
            }
            if ann.args.len() != 1 || ann.args[0].label.is_some() {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`@default` expects exactly one positional argument",
                    )
                    .at(span_to_loc(ann.span)),
                );
            } else if let Some(field_ty) = field_ty
                && let Some(false) = literal_matches_type_annotation(&ann.args[0].value, field_ty)
            {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeMismatch,
                        "`@default` literal does not match field type annotation",
                    )
                    .at(span_to_loc(ann.args[0].value.span)),
                );
            }
        }
        "skip_if" => {
            if !matches!(
                target,
                AnnotationTargetKind::RecordField | AnnotationTargetKind::VariantField
            ) {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!("`@skip_if` is not valid on {}", target.label()),
                    )
                    .at(span_to_loc(ann.span)),
                );
            }
            if ann.args.len() != 1 || ann.args[0].label.is_some() {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`@skip_if` expects exactly one positional predicate argument",
                    )
                    .at(span_to_loc(ann.span)),
                );
            } else if let Some(field_ty) = field_ty
                && is_option_is_none_reference(&ann.args[0].value)
                && !is_optional_annotation(field_ty)
            {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeMismatch,
                        "`@skip_if(Option.is_none)` requires an optional field type",
                    )
                    .at(span_to_loc(ann.args[0].value.span)),
                );
            }
        }
        "tagged" => {
            if !matches!(target, AnnotationTargetKind::TypeDef) {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!("`@tagged` is not valid on {}", target.label()),
                    )
                    .at(span_to_loc(ann.span)),
                );
            }
            if !ann.args.iter().all(|a| a.label.is_some()) {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`@tagged` expects named arguments (e.g. `style: :internal`)",
                    )
                    .at(span_to_loc(ann.span)),
                );
            }
            match named_arg(&ann.args, "style") {
                Some(style) if is_atom_literal_expr(style) => {}
                Some(style) => diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`@tagged` `style:` must be an atom literal",
                    )
                    .at(span_to_loc(style.span)),
                ),
                None => diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`@tagged` requires a `style:` argument",
                    )
                    .at(span_to_loc(ann.span)),
                ),
            }
            if let Some(field) = named_arg(&ann.args, "field")
                && !is_string_literal_expr(field)
            {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`@tagged` `field:` must be a string literal",
                    )
                    .at(span_to_loc(field.span)),
                );
            }
        }
        "deprecated" => {
            if !matches!(
                target,
                AnnotationTargetKind::Function
                    | AnnotationTargetKind::ExprFunction
                    | AnnotationTargetKind::Record
                    | AnnotationTargetKind::TypeDef
            ) {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!("`@deprecated` is not valid on {}", target.label()),
                    )
                    .at(span_to_loc(ann.span)),
                );
            }
            if ann.args.len() > 1 || ann.args.iter().any(|a| a.label.is_some()) {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`@deprecated` accepts at most one positional string argument",
                    )
                    .at(span_to_loc(ann.span)),
                );
            } else if let Some(arg) = first_positional_arg(&ann.args)
                && !is_string_literal_expr(arg)
            {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`@deprecated` message must be a string literal",
                    )
                    .at(span_to_loc(arg.span)),
                );
            }
        }
        _ => {}
    }

    diagnostics
}

pub fn validate_module_annotations(module: &kea_ast::Module) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for decl in &module.declarations {
        match &decl.node {
            kea_ast::DeclKind::Function(fd) => {
                for ann in &fd.annotations {
                    diagnostics.extend(validate_annotation_arguments(
                        ann,
                        AnnotationTargetKind::Function,
                        None,
                    ));
                }
            }
            kea_ast::DeclKind::ExprFn(ed) => {
                for ann in &ed.annotations {
                    diagnostics.extend(validate_annotation_arguments(
                        ann,
                        AnnotationTargetKind::ExprFunction,
                        None,
                    ));
                }
            }
            kea_ast::DeclKind::RecordDef(rd) => {
                let serializable = has_serialize_derive(&rd.derives);
                for ann in &rd.annotations {
                    diagnostics.extend(validate_annotation_arguments(
                        ann,
                        AnnotationTargetKind::Record,
                        None,
                    ));
                }
                for (idx, (_field_name, field_ty)) in rd.fields.iter().enumerate() {
                    let anns = rd.field_annotations.get(idx).cloned().unwrap_or_default();
                    for ann in &anns {
                        diagnostics.extend(validate_annotation_arguments(
                            ann,
                            AnnotationTargetKind::RecordField,
                            Some(field_ty),
                        ));
                        if annotation_is_serialization(&ann.name.node) && !serializable {
                            diagnostics.push(
                                Diagnostic::warning(
                                    Category::TypeError,
                                    format!(
                                        "annotation `@{}` has no effect without `deriving Serialize`",
                                        ann.name.node
                                    ),
                                )
                                .at(span_to_loc(ann.span)),
                            );
                        }
                    }
                }
            }
            kea_ast::DeclKind::TypeDef(td) => {
                let serializable = has_serialize_derive(&td.derives);
                for ann in &td.annotations {
                    diagnostics.extend(validate_annotation_arguments(
                        ann,
                        AnnotationTargetKind::TypeDef,
                        None,
                    ));
                    if annotation_is_serialization(&ann.name.node) && !serializable {
                        diagnostics.push(
                            Diagnostic::warning(
                                Category::TypeError,
                                format!(
                                    "annotation `@{}` has no effect without `deriving Serialize`",
                                    ann.name.node
                                ),
                            )
                            .at(span_to_loc(ann.span)),
                        );
                    }
                }
                for variant in &td.variants {
                    for ann in &variant.annotations {
                        diagnostics.extend(validate_annotation_arguments(
                            ann,
                            AnnotationTargetKind::TypeVariant,
                            None,
                        ));
                        if annotation_is_serialization(&ann.name.node) && !serializable {
                            diagnostics.push(
                                Diagnostic::warning(
                                    Category::TypeError,
                                    format!(
                                        "annotation `@{}` has no effect without `deriving Serialize`",
                                        ann.name.node
                                    ),
                                )
                                .at(span_to_loc(ann.span)),
                            );
                        }
                    }
                    for field in &variant.fields {
                        for ann in &field.annotations {
                            diagnostics.extend(validate_annotation_arguments(
                                ann,
                                AnnotationTargetKind::VariantField,
                                Some(&field.ty.node),
                            ));
                            if annotation_is_serialization(&ann.name.node) && !serializable {
                                diagnostics.push(
                                    Diagnostic::warning(
                                        Category::TypeError,
                                        format!(
                                            "annotation `@{}` has no effect without `deriving Serialize`",
                                            ann.name.node
                                        ),
                                    )
                                    .at(span_to_loc(ann.span)),
                                );
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    diagnostics
}

/// Replace type/row variables according to the given mappings.
fn rename_type(
    ty: &Type,
    type_map: &BTreeMap<TypeVarId, TypeVarId>,
    row_map: &BTreeMap<RowVarId, RowVarId>,
    dim_map: &BTreeMap<DimVarId, DimVarId>,
) -> Type {
    match ty {
        Type::Var(v) => match type_map.get(v) {
            Some(new_v) => Type::Var(*new_v),
            None => ty.clone(),
        },
        Type::List(inner) => Type::List(Box::new(rename_type(inner, type_map, row_map, dim_map))),
        Type::FixedSizeList { element, size } => Type::FixedSizeList {
            element: Box::new(rename_type(element, type_map, row_map, dim_map)),
            size: rename_dim(size, dim_map),
        },
        Type::Tensor { element, shape } => Type::Tensor {
            element: Box::new(rename_type(element, type_map, row_map, dim_map)),
            shape: shape.iter().map(|dim| rename_dim(dim, dim_map)).collect(),
        },
        Type::Set(inner) => Type::Set(Box::new(rename_type(inner, type_map, row_map, dim_map))),
        Type::Option(inner) => {
            Type::Option(Box::new(rename_type(inner, type_map, row_map, dim_map)))
        }
        Type::Map(k, v) => Type::Map(
            Box::new(rename_type(k, type_map, row_map, dim_map)),
            Box::new(rename_type(v, type_map, row_map, dim_map)),
        ),
        Type::Result(ok, err) => Type::Result(
            Box::new(rename_type(ok, type_map, row_map, dim_map)),
            Box::new(rename_type(err, type_map, row_map, dim_map)),
        ),
        Type::Existential {
            bounds,
            associated_types,
        } => Type::Existential {
            bounds: bounds.clone(),
            associated_types: associated_types
                .iter()
                .map(|(name, ty)| (name.clone(), rename_type(ty, type_map, row_map, dim_map)))
                .collect(),
        },
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|t| rename_type(t, type_map, row_map, dim_map))
                .collect(),
        ),
        Type::Function(ft) => Type::Function(FunctionType {
            params: ft
                .params
                .iter()
                .map(|t| rename_type(t, type_map, row_map, dim_map))
                .collect(),
            ret: Box::new(rename_type(&ft.ret, type_map, row_map, dim_map)),
            effects: EffectRow {
                row: rename_row(&ft.effects.row, type_map, row_map, dim_map),
            },
        }),
        Type::Forall(scheme) => {
            let mut scoped_type_map = type_map.clone();
            for tv in &scheme.type_vars {
                scoped_type_map.remove(tv);
            }
            let mut scoped_row_map = row_map.clone();
            for rv in &scheme.row_vars {
                scoped_row_map.remove(rv);
            }
            let mut scoped_dim_map = dim_map.clone();
            for dv in &scheme.dim_vars {
                scoped_dim_map.remove(dv);
            }
            let mut renamed = (**scheme).clone();
            renamed.ty = rename_type(
                &renamed.ty,
                &scoped_type_map,
                &scoped_row_map,
                &scoped_dim_map,
            );
            Type::Forall(Box::new(renamed))
        }
        Type::Record(rt) => Type::Record(kea_types::RecordType {
            name: rt.name.clone(),
            params: rt
                .params
                .iter()
                .map(|t| rename_type(t, type_map, row_map, dim_map))
                .collect(),
            row: rename_row(&rt.row, type_map, row_map, dim_map),
        }),
        Type::AnonRecord(row) => Type::AnonRecord(rename_row(row, type_map, row_map, dim_map)),
        Type::Sum(st) => Type::Sum(kea_types::SumType {
            name: st.name.clone(),
            type_args: st
                .type_args
                .iter()
                .map(|t| rename_type(t, type_map, row_map, dim_map))
                .collect(),
            variants: st
                .variants
                .iter()
                .map(|(vname, fields)| {
                    (
                        vname.clone(),
                        fields
                            .iter()
                            .map(|t| rename_type(t, type_map, row_map, dim_map))
                            .collect(),
                    )
                })
                .collect(),
        }),
        Type::Opaque { name, params } => Type::Opaque {
            name: name.clone(),
            params: params
                .iter()
                .map(|t| rename_type(t, type_map, row_map, dim_map))
                .collect(),
        },
        Type::Row(row) => Type::Row(rename_row(row, type_map, row_map, dim_map)),
        Type::Tagged { inner, tags } => Type::Tagged {
            inner: Box::new(rename_type(inner, type_map, row_map, dim_map)),
            tags: tags.clone(),
        },
        Type::Decimal { precision, scale } => Type::Decimal {
            precision: rename_dim(precision, dim_map),
            scale: rename_dim(scale, dim_map),
        },
        Type::Stream(inner) => {
            Type::Stream(Box::new(rename_type(inner, type_map, row_map, dim_map)))
        }
        Type::Task(inner) => Type::Task(Box::new(rename_type(inner, type_map, row_map, dim_map))),
        Type::Actor(inner) => Type::Actor(Box::new(rename_type(inner, type_map, row_map, dim_map))),
        Type::Arc(inner) => Type::Arc(Box::new(rename_type(inner, type_map, row_map, dim_map))),
        Type::App(constructor, args) => Type::App(
            Box::new(rename_type(constructor, type_map, row_map, dim_map)),
            args.iter()
                .map(|arg| rename_type(arg, type_map, row_map, dim_map))
                .collect(),
        ),
        Type::Constructor {
            name,
            fixed_args,
            arity,
        } => Type::Constructor {
            name: name.clone(),
            fixed_args: fixed_args
                .iter()
                .map(|(idx, ty)| (*idx, rename_type(ty, type_map, row_map, dim_map)))
                .collect(),
            arity: *arity,
        },
        Type::Int
        | Type::IntN(_, _)
        | Type::Float
        | Type::FloatN(_)
        | Type::Bool
        | Type::String
        | Type::Html
        | Type::Markdown
        | Type::Unit
        | Type::Atom
        | Type::Date
        | Type::DateTime
        | Type::Dynamic => ty.clone(),
    }
}

fn rename_row(
    row: &RowType,
    type_map: &BTreeMap<TypeVarId, TypeVarId>,
    row_map: &BTreeMap<RowVarId, RowVarId>,
    dim_map: &BTreeMap<DimVarId, DimVarId>,
) -> RowType {
    let fields = row
        .fields
        .iter()
        .map(|(l, t)| (l.clone(), rename_type(t, type_map, row_map, dim_map)))
        .collect();
    let rest = row.rest.map(|v| *row_map.get(&v).unwrap_or(&v));
    RowType { fields, rest }
}

fn rename_dim(dim: &Dim, dim_map: &BTreeMap<DimVarId, DimVarId>) -> Dim {
    match dim {
        Dim::Known(value) => Dim::Known(*value),
        Dim::Var(v) => Dim::Var(*dim_map.get(v).unwrap_or(v)),
    }
}

// ---------------------------------------------------------------------------
// Type annotation resolution
// ---------------------------------------------------------------------------

fn annotation_label(ann: &TypeAnnotation) -> Option<Label> {
    match ann {
        TypeAnnotation::Named(name) => Some(Label::new(name.clone())),
        _ => None,
    }
}

fn row_annotation_to_type_with<F>(
    fields: &[(String, TypeAnnotation)],
    rest: &Option<String>,
    mut resolve: F,
) -> Option<Type>
where
    F: FnMut(&TypeAnnotation) -> Option<Type>,
{
    let resolved_fields: Option<Vec<(Label, Type)>> = fields
        .iter()
        .map(|(name, ann)| resolve(ann).map(|ty| (Label::new(name.clone()), ty)))
        .collect();
    let resolved_fields = resolved_fields?;

    if let Some(rest_name) = rest {
        let mut row_var_bindings = BTreeMap::new();
        let mut next_row_var = 0u32;
        let rest_var = row_var_from_name(rest_name, &mut row_var_bindings, &mut next_row_var);
        Some(Type::AnonRecord(RowType::open(resolved_fields, rest_var)))
    } else {
        Some(Type::AnonRecord(RowType::closed(resolved_fields)))
    }
}

fn row_annotation_label(fields: &[(String, TypeAnnotation)], rest: &Option<String>) -> String {
    let mut body = fields
        .iter()
        .map(|(name, ty)| format!("{name}: {}", annotation_display(ty)))
        .collect::<Vec<_>>()
        .join(", ");
    if let Some(rest) = rest {
        if body.is_empty() {
            body = format!("| {rest}");
        } else {
            body = format!("{body} | {rest}");
        }
    }
    format!("{{ {body} }}")
}

fn extract_row_type(ty: &Type) -> Option<RowType> {
    match ty {
        Type::Record(rt) => Some(rt.row.clone()),
        Type::AnonRecord(row) | Type::Row(row) => Some(row.clone()),
        _ => None,
    }
}

fn eval_record_type_op<F>(op: &str, args: &[TypeAnnotation], mut resolve: F) -> Option<Type>
where
    F: FnMut(&TypeAnnotation) -> Option<Type>,
{
    match op {
        "Partial" => {
            let [input] = args else {
                return None;
            };
            let row = extract_row_type(&resolve(input)?)?;
            if row.is_open() {
                return None;
            }
            let fields = row
                .fields
                .into_iter()
                .map(|(label, ty)| (label, Type::Option(Box::new(ty))))
                .collect();
            Some(Type::AnonRecord(RowType::closed(fields)))
        }
        "Required" => {
            let [input] = args else {
                return None;
            };
            let row = extract_row_type(&resolve(input)?)?;
            if row.is_open() {
                return None;
            }
            let fields = row
                .fields
                .into_iter()
                .map(|(label, ty)| {
                    let required = match ty {
                        Type::Option(inner) => *inner,
                        other => other,
                    };
                    (label, required)
                })
                .collect();
            Some(Type::AnonRecord(RowType::closed(fields)))
        }
        "Pick" => {
            if args.len() < 2 {
                return None;
            }
            let row = extract_row_type(&resolve(&args[0])?)?;
            let mut picked = Vec::new();
            for ann in &args[1..] {
                let label = annotation_label(ann)?;
                let ty = row.get(&label)?.clone();
                picked.push((label, ty));
            }
            Some(Type::AnonRecord(RowType::closed(picked)))
        }
        "Omit" => {
            if args.len() < 2 {
                return None;
            }
            let row = extract_row_type(&resolve(&args[0])?)?;
            let omit: std::collections::BTreeSet<Label> = args[1..]
                .iter()
                .map(annotation_label)
                .collect::<Option<_>>()?;
            let mut fields: Vec<(Label, Type)> = row
                .fields
                .into_iter()
                .filter(|(label, _)| !omit.contains(label))
                .collect();
            fields.sort_by(|(a, _), (b, _)| a.cmp(b));
            Some(Type::AnonRecord(RowType {
                fields,
                rest: row.rest,
            }))
        }
        "Merge" => {
            let [left, right] = args else {
                return None;
            };
            let left_row = extract_row_type(&resolve(left)?)?;
            let right_row = extract_row_type(&resolve(right)?)?;
            let mut merged: std::collections::BTreeMap<Label, Type> =
                left_row.fields.into_iter().collect();
            for (label, ty) in right_row.fields {
                merged.insert(label, ty);
            }
            let fields: Vec<(Label, Type)> = merged.into_iter().collect();
            Some(Type::AnonRecord(RowType {
                fields,
                rest: right_row.rest.or(left_row.rest),
            }))
        }
        _ => None,
    }
}

fn resolve_named_type_application<F>(
    name: &str,
    args: &[TypeAnnotation],
    records: &RecordRegistry,
    sum_types: Option<&SumTypeRegistry>,
    mut resolve: F,
) -> Option<Type>
where
    F: FnMut(&TypeAnnotation) -> Option<Type>,
{
    let resolved_args: Vec<Type> = args.iter().map(&mut resolve).collect::<Option<Vec<_>>>()?;

    if let Some(alias) = records.lookup_alias(name) {
        if alias.params.len() != resolved_args.len() {
            return None;
        }
        let scope: BTreeMap<String, Type> =
            alias.params.iter().cloned().zip(resolved_args).collect();
        return resolve_annotation_with_type_params(&alias.target, &scope, records, sum_types);
    }

    if let Some(info) = records.lookup_opaque(name) {
        if info.params.len() != resolved_args.len() {
            return None;
        }
        return Some(Type::Opaque {
            name: name.to_string(),
            params: resolved_args,
        });
    }

    if let Some(info) = records.lookup(name) {
        if info.params.len() != resolved_args.len() {
            return None;
        }
        let row = RowType {
            fields: info
                .row
                .fields
                .iter()
                .map(|(label, ty)| {
                    (
                        label.clone(),
                        substitute_params(ty, &info.params, &resolved_args),
                    )
                })
                .collect(),
            rest: info.row.rest,
        };
        return Some(Type::Record(RecordType {
            name: name.to_string(),
            params: resolved_args,
            row,
        }));
    }

    let info = sum_types.and_then(|st| st.lookup(name))?;
    if info.params.len() != resolved_args.len() {
        return None;
    }
    let variants = info
        .variants
        .iter()
        .map(|variant| {
            (
                variant.name.clone(),
                variant
                    .fields
                    .iter()
                    .map(|field_ty| substitute_params(&field_ty.ty, &info.params, &resolved_args))
                    .collect(),
            )
        })
        .collect();
    Some(Type::Sum(SumType {
        name: name.to_string(),
        type_args: resolved_args,
        variants,
    }))
}

fn named_type_param_arity(
    name: &str,
    records: &RecordRegistry,
    sum_types: Option<&SumTypeRegistry>,
) -> Option<usize> {
    // Check built-in constructors first
    if let Some((_, arity)) = BUILTIN_ARITIES.iter().find(|(n, _)| *n == name) {
        return Some(*arity);
    }
    records
        .lookup_alias(name)
        .map(|alias| alias.params.len())
        .or_else(|| records.lookup_opaque(name).map(|info| info.params.len()))
        .or_else(|| records.lookup(name).map(|info| info.params.len()))
        .or_else(|| sum_types.and_then(|st| st.lookup(name).map(|info| info.params.len())))
}

fn annotation_type_arity_mismatch(
    ann: &TypeAnnotation,
    records: &RecordRegistry,
    sum_types: Option<&SumTypeRegistry>,
) -> Option<(String, usize, usize)> {
    match ann {
        TypeAnnotation::Named(name) => {
            let expected = named_type_param_arity(name, records, sum_types)?;
            if expected > 0 {
                Some((name.clone(), expected, 0))
            } else {
                None
            }
        }
        TypeAnnotation::Applied(name, args) => {
            let expected = named_type_param_arity(name, records, sum_types)?;
            let got = args.len();
            if expected == got {
                None
            } else {
                Some((name.clone(), expected, got))
            }
        }
        _ => None,
    }
}

fn push_annotation_arity_mismatch(
    unifier: &mut Unifier,
    span: Span,
    type_name: &str,
    expected: usize,
    got: usize,
) {
    unifier.push_error(
        Diagnostic::error(
            Category::ArityMismatch,
            format!(
                "type `{type_name}` expects {expected} type argument{} but got {got}",
                if expected == 1 { "" } else { "s" }
            ),
        )
        .at(span_to_loc(span)),
    );
}

fn push_annotation_resolution_error(
    unifier: &mut Unifier,
    ann: &TypeAnnotation,
    span: Span,
    records: &RecordRegistry,
    sum_types: Option<&SumTypeRegistry>,
) {
    if let Some((name, expected, got)) = annotation_type_arity_mismatch(ann, records, sum_types) {
        push_annotation_arity_mismatch(unifier, span, &name, expected, got);
        return;
    }
    unifier.push_error(
        Diagnostic::error(
            Category::TypeMismatch,
            format!("unknown type `{}`", annotation_display(ann)),
        )
        .at(span_to_loc(span)),
    );
}

fn decimal_dim_from_annotation_arg(arg: &TypeAnnotation) -> Option<Dim> {
    match arg {
        TypeAnnotation::DimLiteral(n) => Some(Dim::Known(*n)),
        _ => None,
    }
}

/// Known built-in type constructors and their expected arity.
const BUILTIN_ARITIES: &[(&str, usize)] = &[
    ("List", 1),
    ("Option", 1),
    ("Result", 2),
    ("Map", 2),
    ("Set", 1),
    ("Task", 1),
    ("Actor", 1),
    ("Arc", 1),
    ("Stream", 1),
    ("Seq", 1),
    ("Tagged", 1),
    ("Decimal", 2),
];

/// If `name` is a built-in constructor with wrong arity, returns `Some((expected, got))`.
fn builtin_arity_mismatch(name: &str, n_args: usize) -> Option<(usize, usize)> {
    BUILTIN_ARITIES
        .iter()
        .find(|(n, _)| *n == name)
        .and_then(|(_, expected)| {
            if n_args != *expected {
                Some((*expected, n_args))
            } else {
                None
            }
        })
}

fn resolve_decimal_annotation(args: &[TypeAnnotation]) -> Option<Type> {
    let [precision_ann, scale_ann] = args else {
        return None;
    };
    Some(Type::Decimal {
        precision: decimal_dim_from_annotation_arg(precision_ann)?,
        scale: decimal_dim_from_annotation_arg(scale_ann)?,
    })
}

fn fresh_decimal_type(unifier: &mut Unifier) -> Type {
    Type::Decimal {
        precision: Dim::Var(unifier.fresh_dim_var()),
        scale: Dim::Var(unifier.fresh_dim_var()),
    }
}

fn connection_opaque_type() -> Type {
    Type::Opaque {
        name: "Connection".to_string(),
        params: vec![],
    }
}

fn infer_decimal_binary_result_fallback(
    op: BinOp,
    left: &Type,
    right: &Type,
    _unifier: &mut Unifier,
) -> Option<Type> {
    let left_dec = match left {
        Type::Decimal {
            precision: Dim::Known(p),
            scale: Dim::Known(s),
        } => Some((*p, *s)),
        _ => None,
    }?;
    let right_dec = match right {
        Type::Decimal {
            precision: Dim::Known(p),
            scale: Dim::Known(s),
        } => Some((*p, *s)),
        _ => None,
    }?;
    let (lp, ls) = left_dec;
    let (rp, rs) = right_dec;

    let (precision, scale): (i64, i64) = match op {
        BinOp::Add | BinOp::Sub => {
            let int_digits = std::cmp::max(lp - ls, rp - rs);
            let scale = std::cmp::max(ls, rs);
            (int_digits + scale + 1, scale)
        }
        BinOp::Mul => (lp + rp + 1, ls + rs),
        BinOp::Div => {
            let scale = std::cmp::max(6, ls);
            (lp + rs + scale, scale)
        }
        _ => return None,
    };

    let bounded_precision = precision.clamp(1, 38);
    let bounded_scale = scale.clamp(0, bounded_precision);

    Some(Type::Decimal {
        precision: Dim::Known(bounded_precision),
        scale: Dim::Known(bounded_scale),
    })
}

fn instantiate_opaque_target(
    name: &str,
    args: &[Type],
    records: &RecordRegistry,
    sum_types: Option<&SumTypeRegistry>,
) -> Option<Type> {
    let info = records.lookup_opaque(name)?;
    if info.params.len() != args.len() {
        return None;
    }
    let scope: BTreeMap<String, Type> = info
        .params
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    resolve_annotation_with_type_params(&info.target, &scope, records, sum_types)
}

fn collect_annotation_named_types(ann: &TypeAnnotation, out: &mut BTreeSet<String>) {
    match ann {
        TypeAnnotation::Named(name) => {
            out.insert(name.clone());
        }
        TypeAnnotation::Applied(name, args) => {
            out.insert(name.clone());
            for arg in args {
                collect_annotation_named_types(arg, out);
            }
        }
        TypeAnnotation::Row { fields, rest } => {
            for (_, ty) in fields {
                collect_annotation_named_types(ty, out);
            }
            if let Some(rest) = rest {
                out.insert(rest.clone());
            }
        }
        TypeAnnotation::EffectRow(row) => {
            for item in &row.effects {
                out.insert(item.name.clone());
                if let Some(payload) = &item.payload {
                    out.insert(payload.clone());
                }
            }
            if let Some(rest) = &row.rest {
                out.insert(rest.clone());
            }
        }
        TypeAnnotation::Tuple(elems) => {
            for elem in elems {
                collect_annotation_named_types(elem, out);
            }
        }
        TypeAnnotation::Forall { ty, .. } => {
            collect_annotation_named_types(ty, out);
        }
        TypeAnnotation::Function(params, ret)
        | TypeAnnotation::FunctionWithEffect(params, _, ret) => {
            for param in params {
                collect_annotation_named_types(param, out);
            }
            collect_annotation_named_types(ret, out);
        }
        TypeAnnotation::Optional(inner) => collect_annotation_named_types(inner, out),
        TypeAnnotation::Existential {
            associated_types, ..
        } => {
            for (_, ty) in associated_types {
                collect_annotation_named_types(ty, out);
            }
        }
        TypeAnnotation::Projection { .. } | TypeAnnotation::DimLiteral(_) => {}
    }
}

fn build_type_dependency_graph(defs: &[&kea_ast::TypeDef]) -> BTreeMap<String, BTreeSet<String>> {
    let names: BTreeSet<String> = defs.iter().map(|def| def.name.node.clone()).collect();
    let mut graph: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    for def in defs {
        let mut deps = BTreeSet::new();
        for variant in &def.variants {
            for field in &variant.fields {
                let mut named = BTreeSet::new();
                collect_annotation_named_types(&field.ty.node, &mut named);
                deps.extend(named.into_iter().filter(|name| names.contains(name)));
            }
        }
        graph.insert(def.name.node.clone(), deps);
    }

    graph
}

fn strongly_connected_component_map(
    graph: &BTreeMap<String, BTreeSet<String>>,
) -> BTreeMap<String, BTreeSet<String>> {
    fn dfs(
        node: &str,
        graph: &BTreeMap<String, BTreeSet<String>>,
        visited: &mut BTreeSet<String>,
        order: &mut Vec<String>,
    ) {
        if !visited.insert(node.to_string()) {
            return;
        }
        if let Some(neighbors) = graph.get(node) {
            for next in neighbors {
                dfs(next, graph, visited, order);
            }
        }
        order.push(node.to_string());
    }

    fn dfs_rev(
        node: &str,
        reverse: &BTreeMap<String, BTreeSet<String>>,
        visited: &mut BTreeSet<String>,
        component: &mut BTreeSet<String>,
    ) {
        if !visited.insert(node.to_string()) {
            return;
        }
        component.insert(node.to_string());
        if let Some(neighbors) = reverse.get(node) {
            for next in neighbors {
                dfs_rev(next, reverse, visited, component);
            }
        }
    }

    let mut visited = BTreeSet::new();
    let mut order = Vec::new();
    for node in graph.keys() {
        dfs(node, graph, &mut visited, &mut order);
    }

    let mut reverse: BTreeMap<String, BTreeSet<String>> = graph
        .keys()
        .map(|node| (node.clone(), BTreeSet::new()))
        .collect();
    for (from, tos) in graph {
        for to in tos {
            reverse.entry(to.clone()).or_default().insert(from.clone());
        }
    }

    let mut rev_visited = BTreeSet::new();
    let mut component_map = BTreeMap::new();
    while let Some(node) = order.pop() {
        if rev_visited.contains(&node) {
            continue;
        }
        let mut component = BTreeSet::new();
        dfs_rev(&node, &reverse, &mut rev_visited, &mut component);
        for member in &component {
            component_map.insert(member.clone(), component.clone());
        }
    }

    component_map
}

/// Convert a syntactic type annotation to a semantic type.
///
/// Returns `None` for unknown type names.
pub fn resolve_annotation(
    ann: &TypeAnnotation,
    records: &RecordRegistry,
    sum_types: Option<&SumTypeRegistry>,
) -> Option<Type> {
    match ann {
        TypeAnnotation::Named(name) => match name.as_str() {
            "Int" => Some(Type::Int),
            "Int8" => Some(Type::IntN(
                kea_types::IntWidth::I8,
                kea_types::Signedness::Signed,
            )),
            "Int16" => Some(Type::IntN(
                kea_types::IntWidth::I16,
                kea_types::Signedness::Signed,
            )),
            "Int32" => Some(Type::IntN(
                kea_types::IntWidth::I32,
                kea_types::Signedness::Signed,
            )),
            "Int64" => Some(Type::IntN(
                kea_types::IntWidth::I64,
                kea_types::Signedness::Signed,
            )),
            "UInt8" => Some(Type::IntN(
                kea_types::IntWidth::I8,
                kea_types::Signedness::Unsigned,
            )),
            "UInt16" => Some(Type::IntN(
                kea_types::IntWidth::I16,
                kea_types::Signedness::Unsigned,
            )),
            "UInt32" => Some(Type::IntN(
                kea_types::IntWidth::I32,
                kea_types::Signedness::Unsigned,
            )),
            "UInt64" => Some(Type::IntN(
                kea_types::IntWidth::I64,
                kea_types::Signedness::Unsigned,
            )),
            "Float" => Some(Type::Float),
            "Float16" => Some(Type::FloatN(kea_types::FloatWidth::F16)),
            "Float32" => Some(Type::FloatN(kea_types::FloatWidth::F32)),
            "Float64" => Some(Type::FloatN(kea_types::FloatWidth::F64)),
            "Bool" => Some(Type::Bool),
            "String" => Some(Type::String),
            "Html" => Some(Type::Html),
            "Markdown" => Some(Type::Markdown),
            "Unit" => Some(Type::Unit),
            "Atom" => Some(Type::Atom),
            "Date" => Some(Type::Date),
            "DateTime" => Some(Type::DateTime),
            "Dynamic" => Some(Type::Dynamic),
            "Connection" => Some(connection_opaque_type()),
            "IOError" | "SchemaError" | "ExecError" | "ActorError" => {
                kea_types::builtin_error_sum_type(name)
            }
            _ => {
                if let Some(alias) = records.lookup_alias(name) {
                    if !alias.params.is_empty() {
                        return None;
                    }
                    let scope = BTreeMap::new();
                    return resolve_annotation_with_type_params(
                        &alias.target,
                        &scope,
                        records,
                        sum_types,
                    );
                }
                if let Some(info) = records.lookup_opaque(name) {
                    if !info.params.is_empty() {
                        return None;
                    }
                    return Some(Type::Opaque {
                        name: name.clone(),
                        params: vec![],
                    });
                }
                if let Some(sum_info) = sum_types.and_then(|st| st.lookup(name))
                    && !sum_info.params.is_empty()
                {
                    return None;
                }
                records
                    .to_type(name)
                    .or_else(|| sum_types.and_then(|st| st.to_type(name)))
            }
        },
        TypeAnnotation::Applied(name, args) => {
            if let Some(op_ty) = eval_record_type_op(name, args, |ann| {
                resolve_annotation(ann, records, sum_types)
            }) {
                return Some(op_ty);
            }
            if builtin_arity_mismatch(name, args.len()).is_some() {
                return None;
            }
            if name == "Decimal" {
                return resolve_decimal_annotation(args);
            }
            match (name.as_str(), args.as_slice()) {
                ("List", [elem]) => Some(Type::List(Box::new(resolve_annotation(
                    elem, records, sum_types,
                )?))),
                ("Option", [inner]) => Some(Type::Option(Box::new(resolve_annotation(
                    inner, records, sum_types,
                )?))),
                ("Result", [ok, err]) => Some(Type::Result(
                    Box::new(resolve_annotation(ok, records, sum_types)?),
                    Box::new(resolve_annotation(err, records, sum_types)?),
                )),
                ("Map", [key, val]) => Some(Type::Map(
                    Box::new(resolve_annotation(key, records, sum_types)?),
                    Box::new(resolve_annotation(val, records, sum_types)?),
                )),
                ("Set", [elem]) => Some(Type::Set(Box::new(resolve_annotation(
                    elem, records, sum_types,
                )?))),
                ("Actor", [inner]) => Some(Type::Actor(Box::new(resolve_annotation(
                    inner, records, sum_types,
                )?))),
                ("Arc", [inner]) => Some(Type::Arc(Box::new(resolve_annotation(
                    inner, records, sum_types,
                )?))),
                ("Stream", [inner]) => Some(Type::Stream(Box::new(resolve_annotation(
                    inner, records, sum_types,
                )?))),
                ("Task", [inner]) => Some(Type::Task(Box::new(resolve_annotation(
                    inner, records, sum_types,
                )?))),
                ("Step", [inner]) => {
                    let inner_ty = resolve_annotation(inner, records, sum_types)?;
                    Some(Type::Sum(kea_types::SumType {
                        name: "Step".to_string(),
                        type_args: vec![inner_ty.clone()],
                        variants: vec![
                            ("Continue".to_string(), vec![inner_ty.clone()]),
                            ("Halt".to_string(), vec![inner_ty]),
                        ],
                    }))
                }
                ("Tagged", [inner]) => Some(Type::Tagged {
                    inner: Box::new(resolve_annotation(inner, records, sum_types)?),
                    tags: BTreeMap::new(),
                }),
                _ => resolve_named_type_application(name, args, records, sum_types, |arg_ann| {
                    resolve_annotation(arg_ann, records, sum_types)
                }),
            }
        }
        TypeAnnotation::Row { fields, rest } => {
            row_annotation_to_type_with(fields, rest, |field_ann| {
                resolve_annotation(field_ann, records, sum_types)
            })
        }
        TypeAnnotation::EffectRow(_) => None,
        TypeAnnotation::Tuple(elems) => {
            let types: Option<Vec<_>> = elems
                .iter()
                .map(|e| resolve_annotation(e, records, sum_types))
                .collect();
            Some(Type::Tuple(types?))
        }
        TypeAnnotation::Forall { .. } => {
            let scope = BTreeMap::new();
            resolve_annotation_with_type_params(ann, &scope, records, sum_types)
        }
        TypeAnnotation::Function(params, ret) => {
            let param_types: Option<Vec<_>> = params
                .iter()
                .map(|p| resolve_annotation(p, records, sum_types))
                .collect();
            Some(Type::Function(FunctionType {
                params: param_types?,
                ret: Box::new(resolve_annotation(ret, records, sum_types)?),
                effects: EffectRow::pure(),
            }))
        }
        TypeAnnotation::FunctionWithEffect(params, effect, ret) => {
            let param_types: Option<Vec<_>> = params
                .iter()
                .map(|p| resolve_annotation(p, records, sum_types))
                .collect();
            let mut effect_var_bindings = BTreeMap::new();
            let mut next_effect_var = 0u32;
            let effects = function_param_effect_row_from_type_annotation(
                ann,
                &mut effect_var_bindings,
                &mut next_effect_var,
            )
            .or_else(|| effect_annotation_to_compat_row(&effect.node, Some(records)))
            .unwrap_or_else(pure_effect_row);
            Some(Type::Function(FunctionType {
                params: param_types?,
                ret: Box::new(resolve_annotation(ret, records, sum_types)?),
                effects,
            }))
        }
        TypeAnnotation::Optional(inner) => Some(Type::Option(Box::new(resolve_annotation(
            inner, records, sum_types,
        )?))),
        TypeAnnotation::Existential {
            bounds,
            associated_types,
        } => {
            let resolved_assoc: Option<BTreeMap<String, Type>> = associated_types
                .iter()
                .map(|(name, ann)| {
                    resolve_annotation(ann, records, sum_types).map(|ty| (name.clone(), ty))
                })
                .collect();
            Some(Type::Existential {
                bounds: bounds.clone(),
                associated_types: resolved_assoc?,
            })
        }
        // Projection (Self.Name) cannot be resolved without trait/impl context.
        // Return None here; callers with context use resolve_annotation_with_self_and_assoc.
        TypeAnnotation::Projection { .. } => None,
        // DimLiteral only valid inside Applied (handled by resolve_decimal_annotation).
        TypeAnnotation::DimLiteral(_) => None,
    }
}

/// Resolve a type annotation with unifier support for annotation type variables.
fn resolve_annotation_or_bare_df(
    ann: &TypeAnnotation,
    records: &RecordRegistry,
    sum_types: Option<&SumTypeRegistry>,
    unifier: &mut crate::Unifier,
) -> Option<Type> {
    match ann {
        TypeAnnotation::Named(name) => {
            if name == "Record" {
                let row_var = unifier.fresh_row_var();
                return Some(Type::AnonRecord(kea_types::RowType {
                    fields: vec![],
                    rest: Some(row_var),
                }));
            }
            if name == "Decimal" {
                return Some(fresh_decimal_type(unifier));
            }
            if let Some(ty) = unifier.annotation_type_param(name) {
                return Some(ty.clone());
            }
            if let Some(ty) = resolve_annotation(ann, records, sum_types) {
                return Some(ty);
            }
            if looks_like_type_var_name(name) {
                return Some(unifier.annotation_type_param_or_insert_star(name));
            }
            None
        }
        TypeAnnotation::Applied(name, args) => {
            if let Some(constructor_ty) = unifier.annotation_type_param(name).cloned() {
                let resolved_args: Option<Vec<_>> = args
                    .iter()
                    .map(|arg_ann| {
                        resolve_annotation_or_bare_df(arg_ann, records, sum_types, unifier)
                    })
                    .collect();
                return Some(Type::App(Box::new(constructor_ty), resolved_args?));
            }
            if let Some(op_ty) = eval_record_type_op(name, args, |arg_ann| {
                resolve_annotation_or_bare_df(arg_ann, records, sum_types, unifier)
            }) {
                return Some(op_ty);
            }
            if builtin_arity_mismatch(name, args.len()).is_some() {
                return None;
            }
            if name == "Decimal" {
                return resolve_decimal_annotation(args);
            }
            match (name.as_str(), args.as_slice()) {
                ("List", [elem]) => Some(Type::List(Box::new(resolve_annotation_or_bare_df(
                    elem, records, sum_types, unifier,
                )?))),
                ("Option", [inner]) => Some(Type::Option(Box::new(resolve_annotation_or_bare_df(
                    inner, records, sum_types, unifier,
                )?))),
                ("Result", [ok, err]) => Some(Type::Result(
                    Box::new(resolve_annotation_or_bare_df(
                        ok, records, sum_types, unifier,
                    )?),
                    Box::new(resolve_annotation_or_bare_df(
                        err, records, sum_types, unifier,
                    )?),
                )),
                ("Map", [key, val]) => Some(Type::Map(
                    Box::new(resolve_annotation_or_bare_df(
                        key, records, sum_types, unifier,
                    )?),
                    Box::new(resolve_annotation_or_bare_df(
                        val, records, sum_types, unifier,
                    )?),
                )),
                ("Set", [elem]) => Some(Type::Set(Box::new(resolve_annotation_or_bare_df(
                    elem, records, sum_types, unifier,
                )?))),
                ("Actor", [inner]) => Some(Type::Actor(Box::new(resolve_annotation_or_bare_df(
                    inner, records, sum_types, unifier,
                )?))),
                ("Arc", [inner]) => Some(Type::Arc(Box::new(resolve_annotation_or_bare_df(
                    inner, records, sum_types, unifier,
                )?))),
                ("Stream", [inner]) => Some(Type::Stream(Box::new(resolve_annotation_or_bare_df(
                    inner, records, sum_types, unifier,
                )?))),
                ("Task", [inner]) => Some(Type::Task(Box::new(resolve_annotation_or_bare_df(
                    inner, records, sum_types, unifier,
                )?))),
                ("Tagged", [inner]) => Some(Type::Tagged {
                    inner: Box::new(resolve_annotation_or_bare_df(
                        inner, records, sum_types, unifier,
                    )?),
                    tags: BTreeMap::new(),
                }),
                _ => resolve_named_type_application(name, args, records, sum_types, |arg_ann| {
                    resolve_annotation_or_bare_df(arg_ann, records, sum_types, unifier)
                }),
            }
        }
        TypeAnnotation::Row { fields, rest } => {
            row_annotation_to_type_with(fields, rest, |field_ann| {
                resolve_annotation_or_bare_df(field_ann, records, sum_types, unifier)
            })
        }
        TypeAnnotation::EffectRow(_) => None,
        TypeAnnotation::Tuple(elems) => {
            let types: Option<Vec<_>> = elems
                .iter()
                .map(|e| resolve_annotation_or_bare_df(e, records, sum_types, unifier))
                .collect();
            Some(Type::Tuple(types?))
        }
        TypeAnnotation::Forall { type_vars, ty } => {
            let saved_scope = unifier.annotation_type_param_scope.clone();
            let mut scope = saved_scope.clone();
            let mut quantified = Vec::new();
            let mut kinds = BTreeMap::new();
            for name in type_vars {
                let tv = unifier.fresh_type_var_with_kind(Kind::Star);
                scope.insert(name.clone(), Type::Var(tv));
                quantified.push(tv);
                kinds.insert(tv, Kind::Star);
            }
            unifier.set_annotation_type_param_scope(scope);
            let resolved = resolve_annotation_or_bare_df(ty, records, sum_types, unifier);
            unifier.set_annotation_type_param_scope(saved_scope);
            Some(Type::Forall(Box::new(TypeScheme {
                type_vars: quantified,
                row_vars: Vec::new(),
                dim_vars: vec![],
                lacks: BTreeMap::new(),
                bounds: BTreeMap::new(),
                kinds,
                ty: resolved?,
            })))
        }
        TypeAnnotation::Function(params, ret) => {
            let param_types: Option<Vec<_>> = params
                .iter()
                .map(|p| resolve_annotation_or_bare_df(p, records, sum_types, unifier))
                .collect();
            Some(Type::Function(FunctionType {
                params: param_types?,
                ret: Box::new(resolve_annotation_or_bare_df(
                    ret, records, sum_types, unifier,
                )?),
                effects: EffectRow::pure(),
            }))
        }
        TypeAnnotation::FunctionWithEffect(params, effect, ret) => {
            let param_types: Option<Vec<_>> = params
                .iter()
                .map(|p| resolve_annotation_or_bare_df(p, records, sum_types, unifier))
                .collect();
            let mut effect_var_bindings = BTreeMap::new();
            let mut next_effect_var = 0u32;
            let effects = function_param_effect_row_from_type_annotation(
                ann,
                &mut effect_var_bindings,
                &mut next_effect_var,
            )
            .or_else(|| effect_annotation_to_compat_row(&effect.node, Some(records)))
            .or_else(|| {
                effect_annotation_var_name(&effect.node)
                    .map(|_| EffectRow::open(vec![], unifier.fresh_row_var()))
            })
            .unwrap_or_else(pure_effect_row);
            Some(Type::Function(FunctionType {
                params: param_types?,
                ret: Box::new(resolve_annotation_or_bare_df(
                    ret, records, sum_types, unifier,
                )?),
                effects,
            }))
        }
        TypeAnnotation::Optional(inner) => Some(Type::Option(Box::new(
            resolve_annotation_or_bare_df(inner, records, sum_types, unifier)?,
        ))),
        TypeAnnotation::Existential {
            bounds,
            associated_types,
        } => {
            let resolved_assoc: Option<BTreeMap<String, Type>> = associated_types
                .iter()
                .map(|(name, ann)| {
                    resolve_annotation_or_bare_df(ann, records, sum_types, unifier)
                        .map(|ty| (name.clone(), ty))
                })
                .collect();
            Some(Type::Existential {
                bounds: bounds.clone(),
                associated_types: resolved_assoc?,
            })
        }
        TypeAnnotation::Projection { .. } => None,
        TypeAnnotation::DimLiteral(n) => {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "integer literal `{n}` is not valid as a type — \
                         integer arguments are only accepted in dimension-parameterized types like `Decimal(18, 2)`"
                    ),
                ),
            );
            // Return a fresh type var so type checking can continue and report further errors.
            Some(Type::Var(unifier.fresh_type_var()))
        }
    }
}

// ---------------------------------------------------------------------------
// Expression type inference
// ---------------------------------------------------------------------------

fn pure_effect_row() -> EffectRow {
    EffectRow::pure()
}

fn volatile_effect_row() -> EffectRow {
    EffectRow::closed(vec![(Label::new("Volatile"), Type::Unit)])
}

fn impure_effect_row() -> EffectRow {
    EffectRow::closed(vec![(Label::new("IO"), Type::Unit)])
}

fn unknown_effect_row(next_effect_var: &mut u32) -> EffectRow {
    EffectRow::open(vec![], fresh_effect_var(next_effect_var))
}

fn effect_row_from_effects(effects: Effects) -> EffectRow {
    match (effects.purity, effects.volatility) {
        (Purity::Pure, Volatility::Deterministic) => pure_effect_row(),
        (Purity::Pure, Volatility::Volatile) => volatile_effect_row(),
        (Purity::Impure, _) => impure_effect_row(),
    }
}

fn classify_effect_row(row: &EffectRow) -> Effects {
    if row.is_pure() {
        return Effects::pure_deterministic();
    }
    let volatile = Label::new("Volatile");
    let has_volatile = row.row.has(&volatile);
    let has_non_volatile = row.row.fields.iter().any(|(label, _)| label != &volatile);
    if has_non_volatile || row.row.rest.is_some() {
        Effects::impure()
    } else if has_volatile {
        Effects::pure_volatile()
    } else {
        Effects::pure_deterministic()
    }
}

fn fresh_effect_var(next_effect_var: &mut u32) -> RowVarId {
    let var = RowVarId(*next_effect_var);
    *next_effect_var = next_effect_var.saturating_add(1);
    var
}

fn join_effect_rows(
    left: EffectRow,
    right: EffectRow,
    _constraints: &mut Vec<Constraint>,
    next_effect_var: &mut u32,
) -> EffectRow {
    if left.is_pure() {
        return right;
    }
    if right.is_pure() {
        return left;
    }

    let mut merged = BTreeMap::<Label, Type>::new();
    for (label, payload) in &left.row.fields {
        merged.insert(label.clone(), payload.clone());
    }
    for (label, payload) in &right.row.fields {
        if let Some(existing) = merged.get(label) {
            if existing == payload {
                continue;
            }
            continue;
        }
        merged.insert(label.clone(), payload.clone());
    }

    let rest = match (left.row.rest, right.row.rest) {
        (None, None) => None,
        (Some(r), None) | (None, Some(r)) => Some(r),
        (Some(a), Some(b)) if a == b => Some(a),
        (Some(_), Some(_)) => Some(fresh_effect_var(next_effect_var)),
    };

    EffectRow {
        row: RowType {
            fields: merged.into_iter().collect(),
            rest,
        },
    }
}

fn join_effect_rows_many(
    terms: impl IntoIterator<Item = EffectRow>,
    constraints: &mut Vec<Constraint>,
    next_effect_var: &mut u32,
) -> EffectRow {
    terms
        .into_iter()
        .fold(pure_effect_row(), |acc, term| {
            join_effect_rows(acc, term, constraints, next_effect_var)
        })
}

fn effect_row_from_annotation(
    ann: &kea_ast::EffectAnnotation,
    effect_var_bindings: &mut BTreeMap<String, RowVarId>,
    next_effect_var: &mut u32,
) -> Option<EffectRow> {
    match ann {
        kea_ast::EffectAnnotation::Pure => Some(pure_effect_row()),
        // Legacy parse-only forms: checker semantics are row-only.
        kea_ast::EffectAnnotation::Volatile | kea_ast::EffectAnnotation::Impure => None,
        kea_ast::EffectAnnotation::Var(name) => {
            let var = row_var_from_name(name, effect_var_bindings, next_effect_var);
            Some(EffectRow::open(vec![], var))
        }
        kea_ast::EffectAnnotation::Row(row) => {
            let mut visited = BTreeSet::new();
            effect_row_annotation_to_compat_row_with_aliases(
                row,
                None,
                &mut visited,
                effect_var_bindings,
                next_effect_var,
            )
        }
    }
}

fn instantiate_effect_row(
    row: &EffectRow,
    fresh_vars: &mut BTreeMap<RowVarId, RowVarId>,
    next_effect_var: &mut u32,
) -> EffectRow {
    let mut row_map = BTreeMap::new();
    if let Some(rest) = row.row.rest {
        let mapped = *fresh_vars
            .entry(rest)
            .or_insert_with(|| fresh_effect_var(next_effect_var));
        row_map.insert(rest, mapped);
    }
    let type_map = BTreeMap::new();
    let dim_map = BTreeMap::new();
    let fields = row
        .row
        .fields
        .iter()
        .map(|(label, payload)| {
            (
                label.clone(),
                rename_type(payload, &type_map, &row_map, &dim_map),
            )
        })
        .collect::<Vec<_>>();
    let rest = row.row.rest.map(|rv| row_map[&rv]);
    EffectRow {
        row: RowType { fields, rest },
    }
}

fn instantiate_function_effect_signature(
    signature: &FunctionEffectSignature,
    next_effect_var: &mut u32,
) -> FunctionEffectSignature {
    let mut fresh_vars = BTreeMap::new();
    let param_effect_rows = signature
        .param_effect_rows
        .iter()
        .map(|row| {
            row.as_ref()
                .map(|r| instantiate_effect_row(r, &mut fresh_vars, next_effect_var))
        })
        .collect();
    let effect_row = instantiate_effect_row(&signature.effect_row, &mut fresh_vars, next_effect_var);
    FunctionEffectSignature {
        param_effect_rows,
        effect_row,
        instantiate_on_call: signature.instantiate_on_call,
    }
}

fn resolve_effect_call_signature(
    signature: &FunctionEffectSignature,
    next_effect_var: &mut u32,
) -> FunctionEffectSignature {
    if signature.instantiate_on_call {
        instantiate_function_effect_signature(signature, next_effect_var)
    } else {
        signature.clone()
    }
}

fn function_param_effect_row_from_type_annotation(
    ann: &TypeAnnotation,
    effect_var_bindings: &mut BTreeMap<String, RowVarId>,
    next_effect_var: &mut u32,
) -> Option<EffectRow> {
    match ann {
        TypeAnnotation::FunctionWithEffect(_, effect, _) => {
            effect_row_from_annotation(&effect.node, effect_var_bindings, next_effect_var)
        }
        TypeAnnotation::Forall { ty, .. } => function_param_effect_row_from_type_annotation(
            ty,
            effect_var_bindings,
            next_effect_var,
        ),
        _ => None,
    }
}

fn function_effect_signature_from_type_annotation(
    ann: &TypeAnnotation,
    effect_var_bindings: &mut BTreeMap<String, RowVarId>,
    next_effect_var: &mut u32,
) -> Option<FunctionEffectSignature> {
    match ann {
        TypeAnnotation::FunctionWithEffect(params, effect, _ret) => {
            let param_effect_rows = params
                .iter()
                .map(|param_ann| {
                    function_param_effect_row_from_type_annotation(
                        param_ann,
                        effect_var_bindings,
                        next_effect_var,
                    )
                })
                .collect();
            let effect_row =
                effect_row_from_annotation(&effect.node, effect_var_bindings, next_effect_var)?;
            Some(FunctionEffectSignature {
                param_effect_rows,
                effect_row,
                instantiate_on_call: false,
            })
        }
        // Keep local callback linkage for rank-2/forall-wrapped function params.
        TypeAnnotation::Forall { ty, .. } => {
            function_effect_signature_from_type_annotation(ty, effect_var_bindings, next_effect_var)
        }
        _ => None,
    }
}

/// Build a function effect-signature template from declaration annotations.
///
/// Returns `None` when the function has no declared effect annotation.
pub fn function_effect_signature_from_decl(fn_decl: &FnDecl) -> Option<FunctionEffectSignature> {
    let effect_ann = fn_decl.effect_annotation.as_ref()?;
    let mut effect_var_bindings = BTreeMap::new();
    let mut next_effect_var = 0u32;
    let param_effect_rows = fn_decl
        .params
        .iter()
        .map(|param| {
            param.annotation.as_ref().and_then(|ann| {
                function_param_effect_row_from_type_annotation(
                    &ann.node,
                    &mut effect_var_bindings,
                    &mut next_effect_var,
                )
            })
        })
        .collect();
    let effect_row = effect_row_from_annotation(
        &effect_ann.node,
        &mut effect_var_bindings,
        &mut next_effect_var,
    )?;
    Some(FunctionEffectSignature {
        param_effect_rows,
        effect_row,
        instantiate_on_call: true,
    })
}

/// Build a function effect-signature from a registered trait method.
///
/// Uses the method's `declared_effect` and parameter annotations to
/// produce a `FunctionEffectSignature`, paralleling `function_effect_signature_from_decl`.
pub fn function_effect_signature_from_trait_method(
    method: &TraitMethodInfo,
) -> Option<FunctionEffectSignature> {
    let effect_ann = method.declared_effect.as_ref()?;
    let mut effect_var_bindings = BTreeMap::new();
    let mut next_effect_var = 0u32;
    let param_effect_rows = method
        .params
        .iter()
        .map(|param| {
            param.annotation.as_ref().and_then(|ann| {
                function_param_effect_row_from_type_annotation(
                    &ann.node,
                    &mut effect_var_bindings,
                    &mut next_effect_var,
                )
            })
        })
        .collect();
    let effect_row = effect_row_from_annotation(
        effect_ann,
        &mut effect_var_bindings,
        &mut next_effect_var,
    )?;
    Some(FunctionEffectSignature {
        param_effect_rows,
        effect_row,
        instantiate_on_call: true,
    })
}

fn function_signature_from_params(params: &[Param]) -> FnSignature {
    FnSignature {
        params: params
            .iter()
            .map(|param| FnParamSignature {
                name: param.name().map(ToOwned::to_owned),
                label: param.effective_label().map(ToOwned::to_owned),
                default: param.default.clone(),
            })
            .collect(),
    }
}

/// Build call-site signature metadata from a function declaration.
pub fn function_signature_from_decl(fn_decl: &FnDecl) -> FnSignature {
    function_signature_from_params(&fn_decl.params)
}

/// Register declaration-derived call-signature metadata in the type env.
pub fn register_fn_signature(fn_decl: &FnDecl, env: &mut TypeEnv) {
    env.set_function_signature(
        fn_decl.name.node.clone(),
        function_signature_from_decl(fn_decl),
    );
}

/// Register a declaration-derived effect-signature template in the type env.
pub fn register_fn_effect_signature(fn_decl: &FnDecl, env: &mut TypeEnv) {
    register_fn_signature(fn_decl, env);
    if let Some(signature) = function_effect_signature_from_decl(fn_decl) {
        env.set_function_effect_signature(fn_decl.name.node.clone(), signature);
    }
}

/// Register an effect declaration's operations as qualified call targets.
///
/// Effect operation calls are always effectful with the declared effect label,
/// so each registered operation gets an effect-signature template whose row is
/// `[EffectName]`.
pub fn register_effect_decl(
    effect_decl: &EffectDecl,
    records: &RecordRegistry,
    sum_types: Option<&SumTypeRegistry>,
    env: &mut TypeEnv,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let module_short = effect_decl.name.node.clone();
    let module_path = format!("Kea.{module_short}");
    env.register_module_alias(&module_short, &module_path);

    let mut type_param_scope = BTreeMap::new();
    let mut type_vars = Vec::new();
    let mut kinds = BTreeMap::new();
    let mut seen_params = BTreeSet::new();
    let mut next_placeholder = u32::MAX;
    for type_param in &effect_decl.type_params {
        if !seen_params.insert(type_param.clone()) {
            diagnostics.push(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "duplicate effect type parameter `{type_param}` in effect `{module_short}`"
                    ),
                )
                .at(span_to_loc(effect_decl.name.span)),
            );
            continue;
        }
        let tv = TypeVarId(next_placeholder);
        next_placeholder = next_placeholder.wrapping_sub(1);
        type_param_scope.insert(type_param.clone(), Type::Var(tv));
        type_vars.push(tv);
        kinds.insert(tv, Kind::Star);
    }

    for op in &effect_decl.operations {
        let mut param_tys = Vec::with_capacity(op.params.len());
        let mut missing_param_annotations = Vec::new();
        for (idx, param) in op.params.iter().enumerate() {
            let Some(annotation) = &param.annotation else {
                missing_param_annotations.push(idx + 1);
                continue;
            };
            let Some(param_ty) = resolve_annotation_with_type_params(
                &annotation.node,
                &type_param_scope,
                records,
                sum_types,
            ) else {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!(
                            "unknown type in parameter {} of effect operation `{}`",
                            idx + 1,
                            op.name.node
                        ),
                    )
                    .at(span_to_loc(annotation.span)),
                );
                continue;
            };
            param_tys.push(param_ty);
        }
        if !missing_param_annotations.is_empty() {
            diagnostics.push(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "effect operation `{}` is missing type annotations for parameter(s) {}",
                        op.name.node,
                        missing_param_annotations
                            .iter()
                            .map(|idx| idx.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                )
                .at(span_to_loc(op.span)),
            );
            continue;
        }
        if param_tys.len() != op.params.len() {
            continue;
        }

        let Some(ret_ty) = resolve_annotation_with_type_params(
            &op.return_annotation.node,
            &type_param_scope,
            records,
            sum_types,
        ) else {
            diagnostics.push(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "unknown return type in effect operation `{}`",
                        op.name.node
                    ),
                )
                .at(span_to_loc(op.return_annotation.span)),
            );
            continue;
        };

        let op_ty = Type::Function(FunctionType {
            params: param_tys,
            ret: Box::new(ret_ty),
            effects: EffectRow::closed(vec![(Label::new(module_short.clone()), Type::Unit)]),
        });
        let op_scheme = TypeScheme {
            type_vars: type_vars.clone(),
            row_vars: Vec::new(),
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: kinds.clone(),
            ty: op_ty,
        };

        env.register_module_function(&module_path, &op.name.node);
        env.register_module_type_scheme(
            &module_path,
            &op.name.node,
            op_scheme,
            Effects::impure(),
        );

        let qualified_name = format!("{module_path}::{}", op.name.node);
        env.set_function_signature(qualified_name.clone(), function_signature_from_params(&op.params));

        let mut effect_var_bindings = BTreeMap::new();
        let mut next_effect_var = 0u32;
        let param_effect_rows = op
            .params
            .iter()
            .map(|param| {
                param.annotation.as_ref().and_then(|ann| {
                    function_param_effect_row_from_type_annotation(
                        &ann.node,
                        &mut effect_var_bindings,
                        &mut next_effect_var,
                    )
                })
            })
            .collect();
        env.set_function_effect_signature(
            qualified_name,
            FunctionEffectSignature {
                param_effect_rows,
                effect_row: EffectRow::closed(vec![(Label::new(module_short.clone()), Type::Unit)]),
                instantiate_on_call: true,
            },
        );
    }

    diagnostics
}

fn seed_function_param_effect_rows(
    params: &[Param],
    env: &mut TypeEnv,
    effect_var_bindings: &mut BTreeMap<String, RowVarId>,
    next_effect_var: &mut u32,
) {
    for param in params {
        let Some(param_name) = param.name() else {
            continue;
        };
        let Some(ann) = &param.annotation else {
            continue;
        };
        if let Some(signature) = function_effect_signature_from_type_annotation(
            &ann.node,
            effect_var_bindings,
            next_effect_var,
        ) {
            env.set_function_effect_signature(param_name.to_string(), signature.clone());
            env.set_function_effect_row(param_name.to_string(), signature.effect_row);
        }
    }
}

fn infer_lambda_effect_row(
    params: &[Param],
    body: &Expr,
    env: &TypeEnv,
    constraints: &mut Vec<Constraint>,
    next_effect_var: &mut u32,
) -> EffectRow {
    let mut lambda_env = env.clone();
    let mut lambda_effect_vars = BTreeMap::new();
    seed_function_param_effect_rows(
        params,
        &mut lambda_env,
        &mut lambda_effect_vars,
        next_effect_var,
    );
    infer_expr_effect_row(body, &lambda_env, constraints, next_effect_var)
}

fn infer_lambda_effect_signature(
    params: &[Param],
    body: &Expr,
    env: &TypeEnv,
    constraints: &mut Vec<Constraint>,
    next_effect_var: &mut u32,
) -> FunctionEffectSignature {
    let mut lambda_env = env.clone();
    let mut lambda_effect_vars = BTreeMap::new();
    seed_function_param_effect_rows(
        params,
        &mut lambda_env,
        &mut lambda_effect_vars,
        next_effect_var,
    );
    let param_effect_rows = params
        .iter()
        .map(|param| {
            param.annotation.as_ref().and_then(|ann| {
                function_param_effect_row_from_type_annotation(
                    &ann.node,
                    &mut lambda_effect_vars,
                    next_effect_var,
                )
            })
        })
        .collect();
    let effect_row = infer_expr_effect_row(body, &lambda_env, constraints, next_effect_var);
    FunctionEffectSignature {
        param_effect_rows,
        effect_row,
        instantiate_on_call: false,
    }
}

fn infer_callable_value_effect_row(
    expr: &Expr,
    env: &TypeEnv,
    constraints: &mut Vec<Constraint>,
    next_effect_var: &mut u32,
) -> EffectRow {
    match &expr.node {
        ExprKind::Var(name) => {
            if let Some(signature) = env.function_effect_signature(name) {
                resolve_effect_call_signature(signature, next_effect_var).effect_row
            } else {
                env.function_effect_row(name)
                    .unwrap_or_else(|| unknown_effect_row(next_effect_var))
            }
        }
        ExprKind::Lambda { params, body, .. } => {
            infer_lambda_effect_row(params, body, env, constraints, next_effect_var)
        }
        ExprKind::FieldAccess { expr, field } => {
            if let ExprKind::Var(module) = &expr.node {
                if let Some(signature) = env.resolve_qualified_effect_signature(module, &field.node)
                {
                    resolve_effect_call_signature(signature, next_effect_var).effect_row
                } else {
                    env.resolve_qualified_effect_row(module, &field.node)
                        .unwrap_or_else(|| unknown_effect_row(next_effect_var))
                }
            } else {
                unknown_effect_row(next_effect_var)
            }
        }
        _ => infer_expr_effect_row(expr, env, constraints, next_effect_var),
    }
}

fn function_effect_signature_from_type(ty: &Type) -> Option<FunctionEffectSignature> {
    match ty {
        Type::Function(ft) => Some(FunctionEffectSignature {
            param_effect_rows: ft
                .params
                .iter()
                .map(TypeEnv::effect_row_from_type)
                .collect(),
            effect_row: ft.effects.clone(),
            instantiate_on_call: false,
        }),
        Type::Forall(inner) => function_effect_signature_from_type(&inner.ty),
        _ => None,
    }
}

fn callable_effect_metadata_from_call_return_type(
    callee_ty: &Type,
    next_effect_var: &mut u32,
) -> (Option<EffectRow>, Option<FunctionEffectSignature>) {
    match callee_ty {
        Type::Function(ft) => {
            let signature = function_effect_signature_from_type(&ft.ret).map(|sig| {
                instantiate_function_effect_signature(&sig, next_effect_var)
            });
            let term = signature.as_ref().map(|sig| sig.effect_row.clone());
            (term, signature)
        }
        Type::Forall(inner) => {
            callable_effect_metadata_from_call_return_type(&inner.ty, next_effect_var)
        }
        _ => (None, None),
    }
}

fn callable_effect_metadata_from_call(
    func: &Expr,
    env: &TypeEnv,
    next_effect_var: &mut u32,
) -> (Option<EffectRow>, Option<FunctionEffectSignature>) {
    match &func.node {
        ExprKind::Var(name) => env
            .lookup(name)
            .map(|scheme| {
                callable_effect_metadata_from_call_return_type(&scheme.ty, next_effect_var)
            })
            .unwrap_or((None, None)),
        ExprKind::FieldAccess { expr, field } => {
            if let ExprKind::Var(module) = &expr.node {
                env.resolve_qualified(module, &field.node)
                    .map(|scheme| {
                        callable_effect_metadata_from_call_return_type(
                            &scheme.ty,
                            next_effect_var,
                        )
                    })
                    .unwrap_or((None, None))
            } else {
                (None, None)
            }
        }
        _ => (None, None),
    }
}

fn bind_let_pattern_effect_metadata(
    pattern: &Pattern,
    callable_term: Option<EffectRow>,
    callable_signature: Option<FunctionEffectSignature>,
    env: &mut TypeEnv,
) {
    let PatternKind::Var(bound_name) = &pattern.node else {
        return;
    };

    if let Some(signature) = callable_signature {
        env.set_function_effect_signature(bound_name.clone(), signature);
    }
    if let Some(term) = callable_term {
        env.set_function_effect_row(bound_name.clone(), term);
    }
}

fn infer_call_effect_row(
    func: &Expr,
    args: &[Argument],
    env: &TypeEnv,
    constraints: &mut Vec<Constraint>,
    next_effect_var: &mut u32,
) -> EffectRow {
    let effect_signature = match &func.node {
        ExprKind::Var(name) => env.function_effect_signature(name),
        ExprKind::FieldAccess { expr, field } => {
            if let ExprKind::Var(module) = &expr.node {
                env.resolve_qualified_effect_signature(module, &field.node)
            } else {
                None
            }
        }
        _ => None,
    };

    if let Some(effect_signature) = effect_signature {
        let call_signature = resolve_call_signature(func, env);
        let fallback = args
            .iter()
            .map(|arg| BoundArg::Provided(arg.value.clone()))
            .collect::<Vec<_>>();
        let bound_args = if let Some(sig) = call_signature {
            bind_args(sig, args).unwrap_or(fallback)
        } else {
            fallback
        };

        let instantiated = resolve_effect_call_signature(effect_signature, next_effect_var);
        for (idx, maybe_param_effect) in instantiated.param_effect_rows.iter().enumerate() {
            let Some(param_effect) = maybe_param_effect else {
                continue;
            };
            let Some(arg_expr) = bound_args.get(idx).map(bound_arg_expr) else {
                continue;
            };
            let arg_callable_effect =
                infer_callable_value_effect_row(arg_expr, env, constraints, next_effect_var);
            constraints.push(Constraint::RowEqual {
                expected: param_effect.row.clone(),
                actual: arg_callable_effect.row,
                provenance: Provenance {
                    span: arg_expr.span,
                    reason: Reason::TypeAscription,
                },
            });
        }
        return instantiated.effect_row;
    }

    match &func.node {
        ExprKind::Var(name) => env
            .function_effect_row(name)
            .unwrap_or_else(|| unknown_effect_row(next_effect_var)),
        ExprKind::Lambda { params, body, .. } => {
            infer_lambda_effect_row(params, body, env, constraints, next_effect_var)
        }
        ExprKind::FieldAccess { expr, field } => {
            if let ExprKind::Var(module) = &expr.node {
                env.resolve_qualified_effect_row(module, &field.node)
                    .unwrap_or_else(|| unknown_effect_row(next_effect_var))
            } else {
                unknown_effect_row(next_effect_var)
            }
        }
        _ => unknown_effect_row(next_effect_var),
    }
}

/// Infer effects bottom-up for a function declaration's bodies.
///
/// Uses a small fixed-point iteration so recursive functions can reference
/// their own inferred effects.
pub fn infer_fn_decl_effect_row(fn_decl: &FnDecl, env: &TypeEnv) -> EffectRow {
    let name = fn_decl.name.node.clone();
    let mut trial_env = env.clone();
    let mut current = trial_env
        .function_effect_row(&name)
        .unwrap_or_else(pure_effect_row);

    // Small fixed-point loop for recursion.
    for _ in 0..4 {
        trial_env.set_function_effect_row(name.clone(), current.clone());
        let mut effect_var_bindings = BTreeMap::new();
        let mut next_effect_var = 0u32;
        seed_function_param_effect_rows(
            &fn_decl.params,
            &mut trial_env,
            &mut effect_var_bindings,
            &mut next_effect_var,
        );
        let mut constraints = Vec::new();
        let root = infer_expr_effect_row(
            &fn_decl.body,
            &trial_env,
            &mut constraints,
            &mut next_effect_var,
        );
        let next = {
            let mut unifier = Unifier::new();
            if unifier.solve(constraints).is_err() {
                impure_effect_row()
            } else {
                EffectRow {
                    row: unifier.substitution.apply_row(&root.row),
                }
            }
        };
        if next == current {
            break;
        }
        current = next;
    }

    current
}

pub fn infer_fn_decl_effects(fn_decl: &FnDecl, env: &TypeEnv) -> Effects {
    classify_effect_row(&infer_fn_decl_effect_row(fn_decl, env))
}

fn parse_declared_effect(
    ann: &kea_ast::Spanned<kea_ast::EffectAnnotation>,
) -> kea_ast::EffectAnnotation {
    parse_effect_annotation(ann)
}

fn parse_effect_annotation(
    ann: &kea_ast::Spanned<kea_ast::EffectAnnotation>,
) -> kea_ast::EffectAnnotation {
    ann.node.clone()
}

fn effect_row_annotation_label(row: &kea_ast::EffectRowAnnotation) -> String {
    let mut body = row
        .effects
        .iter()
        .map(|item| match &item.payload {
            Some(payload) => format!("{} {}", item.name, payload),
            None => item.name.clone(),
        })
        .collect::<Vec<_>>()
        .join(", ");
    if let Some(rest) = &row.rest {
        if body.is_empty() {
            body = format!("| {}", rest);
        } else {
            body = format!("{body} | {rest}");
        }
    }
    format!("[{body}]")
}

fn effect_item_name_to_compat_row(name: &str) -> EffectRow {
    EffectRow::closed(vec![(Label::new(name), Type::Unit)])
}

fn resolve_effect_payload_type(payload: &str, records: Option<&RecordRegistry>) -> Option<Type> {
    let payload_ann = TypeAnnotation::Named(payload.to_string());
    if let Some(records) = records {
        return resolve_annotation(&payload_ann, records, None);
    }
    let empty_records = RecordRegistry::new();
    resolve_annotation(&payload_ann, &empty_records, None)
}

fn row_var_from_name(
    name: &str,
    row_var_bindings: &mut BTreeMap<String, RowVarId>,
    next_row_var: &mut u32,
) -> RowVarId {
    *row_var_bindings.entry(name.to_string()).or_insert_with(|| {
        let id = RowVarId(*next_row_var);
        *next_row_var = next_row_var.saturating_add(1);
        id
    })
}

fn effect_alias_target_to_compat_row(
    target: &TypeAnnotation,
    records: &RecordRegistry,
    visited_aliases: &mut BTreeSet<String>,
    row_var_bindings: &mut BTreeMap<String, RowVarId>,
    next_row_var: &mut u32,
) -> Option<EffectRow> {
    match target {
        TypeAnnotation::EffectRow(row) => effect_row_annotation_to_compat_row_with_aliases(
            row,
            Some(records),
            visited_aliases,
            row_var_bindings,
            next_row_var,
        ),
        TypeAnnotation::Named(name) => {
            if let Some(alias) = records.lookup_alias(name)
                && alias.params.is_empty()
                && visited_aliases.insert(name.clone())
            {
                let expanded = effect_alias_target_to_compat_row(
                    &alias.target,
                    records,
                    visited_aliases,
                    row_var_bindings,
                    next_row_var,
                );
                visited_aliases.remove(name);
                return expanded.or_else(|| Some(effect_item_name_to_compat_row(name)));
            }
            Some(effect_item_name_to_compat_row(name))
        }
        _ => None,
    }
}

fn effect_row_item_to_compat_row(
    item: &kea_ast::EffectRowItem,
    records: Option<&RecordRegistry>,
    visited_aliases: &mut BTreeSet<String>,
    row_var_bindings: &mut BTreeMap<String, RowVarId>,
    next_row_var: &mut u32,
) -> Option<EffectRow> {
    if item.name == "Fail" {
        let payload = match &item.payload {
            Some(name) => resolve_effect_payload_type(name, records)?,
            None => Type::Unit,
        };
        return Some(EffectRow::closed(vec![(Label::new("Fail"), payload)]));
    }

    if item.payload.is_none()
        && let Some(records) = records
        && let Some(alias) = records.lookup_alias(&item.name)
        && alias.params.is_empty()
        && visited_aliases.insert(item.name.clone())
    {
        let expanded = effect_alias_target_to_compat_row(
            &alias.target,
            records,
            visited_aliases,
            row_var_bindings,
            next_row_var,
        );
        visited_aliases.remove(&item.name);
        return expanded;
    }

    Some(effect_item_name_to_compat_row(&item.name))
}

fn append_effect_row_fields_unique(
    out: &mut Vec<(Label, Type)>,
    row: &EffectRow,
) -> Result<(), String> {
    let fail_label = Label::new("Fail");
    for (label, payload) in &row.row.fields {
        if let Some((_, existing_payload)) = out.iter().find(|(existing, _)| existing == label) {
            if label == &fail_label {
                if existing_payload == payload {
                    continue;
                }
                // Keep mismatched duplicate Fail payloads so dedicated
                // validation can surface a conversion-oriented diagnostic.
                out.push((label.clone(), payload.clone()));
                continue;
            }
            return Err(label.to_string());
        }
        out.push((label.clone(), payload.clone()));
    }
    Ok(())
}

fn effect_row_annotation_to_compat_row_with_aliases(
    row: &kea_ast::EffectRowAnnotation,
    records: Option<&RecordRegistry>,
    visited_aliases: &mut BTreeSet<String>,
    row_var_bindings: &mut BTreeMap<String, RowVarId>,
    next_row_var: &mut u32,
) -> Option<EffectRow> {
    let mut fields = Vec::new();
    let mut alias_rest = None;

    for item in &row.effects {
        let item_row = effect_row_item_to_compat_row(
            item,
            records,
            visited_aliases,
            row_var_bindings,
            next_row_var,
        )?;
        if append_effect_row_fields_unique(&mut fields, &item_row).is_err() {
            return None;
        }
        if let Some(rest) = item_row.row.rest {
            if alias_rest.is_some() {
                return None;
            }
            alias_rest = Some(rest);
        }
    }

    let merged_rest = match (row.rest.clone(), alias_rest) {
        (Some(_), Some(_)) => return None,
        (Some(rest), None) => Some(row_var_from_name(&rest, row_var_bindings, next_row_var)),
        (None, rest) => rest,
    };

    if let Some(rest) = merged_rest {
        Some(EffectRow {
            row: RowType::open(fields, rest),
        })
    } else {
        Some(EffectRow::closed(fields))
    }
}

fn effect_row_annotation_to_compat_row(row: &kea_ast::EffectRowAnnotation) -> Option<EffectRow> {
    let mut visited = BTreeSet::new();
    let mut row_var_bindings = BTreeMap::new();
    let mut next_row_var = 0u32;
    effect_row_annotation_to_compat_row_with_aliases(
        row,
        None,
        &mut visited,
        &mut row_var_bindings,
        &mut next_row_var,
    )
}

fn effect_annotation_var_name(effect: &kea_ast::EffectAnnotation) -> Option<&str> {
    match effect {
        kea_ast::EffectAnnotation::Var(name) => Some(name.as_str()),
        // Compatibility: treat `-[e]>` and `-[| e]>` equivalently.
        kea_ast::EffectAnnotation::Row(row) if row.effects.is_empty() => row.rest.as_deref(),
        _ => None,
    }
}

fn effect_annotation_label(effect: &kea_ast::EffectAnnotation) -> String {
    match effect {
        kea_ast::EffectAnnotation::Pure => "pure".to_string(),
        kea_ast::EffectAnnotation::Volatile => "volatile".to_string(),
        kea_ast::EffectAnnotation::Impure => "impure".to_string(),
        kea_ast::EffectAnnotation::Var(name) => name.clone(),
        kea_ast::EffectAnnotation::Row(row) => effect_row_annotation_label(row),
    }
}

fn effect_annotation_to_compat_row(
    effect: &kea_ast::EffectAnnotation,
    records: Option<&RecordRegistry>,
) -> Option<EffectRow> {
    match effect {
        kea_ast::EffectAnnotation::Pure => Some(pure_effect_row()),
        // Legacy parse-only forms: checker semantics are row-only.
        kea_ast::EffectAnnotation::Volatile | kea_ast::EffectAnnotation::Impure => None,
        kea_ast::EffectAnnotation::Var(_) => None,
        kea_ast::EffectAnnotation::Row(row) => {
            if let Some(records) = records {
                let mut visited = BTreeSet::new();
                let mut row_var_bindings = BTreeMap::new();
                let mut next_row_var = 0u32;
                effect_row_annotation_to_compat_row_with_aliases(
                    row,
                    Some(records),
                    &mut visited,
                    &mut row_var_bindings,
                    &mut next_row_var,
                )
            } else {
                effect_row_annotation_to_compat_row(row)
            }
        }
    }
}

fn validate_effect_row_fail_cardinality(
    row: &EffectRow,
    span: Span,
    context: &str,
) -> Result<(), Diagnostic> {
    let fail_label = Label::new("Fail");
    let fail_payloads = row
        .row
        .fields
        .iter()
        .filter_map(|(label, payload)| (label == &fail_label).then_some(payload))
        .collect::<Vec<_>>();
    if fail_payloads.len() <= 1 {
        return Ok(());
    }

    let first = fail_payloads[0].clone();
    if fail_payloads
        .iter()
        .skip(1)
        .all(|payload| payload == &&first)
    {
        return Ok(());
    }

    Err(
        Diagnostic::error(
            Category::TypeMismatch,
            format!("effect row `{context}` contains multiple incompatible `Fail` entries"),
        )
        .at(span_to_loc(span))
        .with_help(
            "effect rows allow at most one `Fail` payload type; unify them or convert with `From`",
        ),
    )
}

fn effect_row_fail_payload(row: &EffectRow) -> Option<&Type> {
    row.row
        .fields
        .iter()
        .find(|(label, _)| label == &Label::new("Fail"))
        .map(|(_, payload)| payload)
}

fn instantiate_effect_row_for_unifier(row: &EffectRow, unifier: &mut Unifier) -> EffectRow {
    let mut row_map = BTreeMap::new();
    if let Some(rest) = row.row.rest {
        row_map
            .entry(rest)
            .or_insert_with(|| unifier.fresh_row_var());
    }
    let type_map = BTreeMap::new();
    let dim_map = BTreeMap::new();
    let fields = row
        .row
        .fields
        .iter()
        .map(|(label, payload)| {
            (
                label.clone(),
                rename_type(payload, &type_map, &row_map, &dim_map),
            )
        })
        .collect();
    let rest = row
        .row
        .rest
        .and_then(|rv| row_map.get(&rv).copied());
    EffectRow {
        row: RowType { fields, rest },
    }
}

pub(crate) fn unify_effect_row_subsumption(
    actual: &EffectRow,
    declared: &EffectRow,
    span: Span,
) -> Result<(), Diagnostic> {
    if let (Some(actual_fail), Some(declared_fail)) = (
        effect_row_fail_payload(actual),
        effect_row_fail_payload(declared),
    ) && actual_fail != declared_fail
    {
        return Err(
            Diagnostic::error(
                Category::TypeMismatch,
                format!(
                    "effect rows use incompatible `Fail` payloads: inferred `{actual_fail}`, declared `{declared_fail}`"
                ),
            )
            .at(span_to_loc(span))
            .with_help(format!(
                "implement `From<{actual_fail}> for {declared_fail}` or use `catch` to handle `{actual_fail}` explicitly"
            )),
        );
    }

    let mut unifier = Unifier::new();
    let declared = instantiate_effect_row_for_unifier(declared, &mut unifier);
    let actual_tail = unifier.fresh_row_var();
    let widened_actual = RowType::open(actual.row.fields.clone(), actual_tail);
    let mut constraints = vec![Constraint::RowEqual {
        expected: declared.row.clone(),
        actual: widened_actual,
        provenance: Provenance {
            span,
            reason: Reason::TypeAscription,
        },
    }];

    let fail_label = Label::new("Fail");
    if actual.row.has(&fail_label) {
        constraints.push(Constraint::Lacks {
            var: actual_tail,
            label: fail_label.clone(),
            provenance: Provenance {
                span,
                reason: Reason::RowExtension {
                    label: fail_label.clone(),
                },
            },
        });
    }
    if declared.row.has(&fail_label)
        && let Some(rest) = declared.row.rest
    {
        constraints.push(Constraint::Lacks {
            var: rest,
            label: fail_label,
            provenance: Provenance {
                span,
                reason: Reason::RowExtension {
                    label: Label::new("Fail"),
                },
            },
        });
    }

    unifier.solve(constraints).map_err(|solve_err| {
        let mut diag = Diagnostic::error(
            Category::TypeMismatch,
            "declared effect row is too weak for the inferred body effects",
        )
        .at(span_to_loc(span));
        if let Some(first) = solve_err.diagnostics().first() {
            diag = diag.with_help(first.message.clone());
        }
        diag
    })?;
    Ok(())
}

fn type_annotation_has_effect_var(ann: &TypeAnnotation, target: &str) -> bool {
    match ann {
        TypeAnnotation::FunctionWithEffect(params, effect, ret) => {
            let current_matches = effect_annotation_var_name(&effect.node) == Some(target);
            current_matches
                || params
                    .iter()
                    .any(|param| type_annotation_has_effect_var(param, target))
                || type_annotation_has_effect_var(ret, target)
        }
        TypeAnnotation::Function(params, ret) => {
            params
                .iter()
                .any(|param| type_annotation_has_effect_var(param, target))
                || type_annotation_has_effect_var(ret, target)
        }
        TypeAnnotation::Forall { ty, .. } => type_annotation_has_effect_var(ty, target),
        TypeAnnotation::Applied(_, args) | TypeAnnotation::Tuple(args) => args
            .iter()
            .any(|arg| type_annotation_has_effect_var(arg, target)),
        TypeAnnotation::Row { fields, .. } => fields
            .iter()
            .any(|(_, ty)| type_annotation_has_effect_var(ty, target)),
        TypeAnnotation::EffectRow(row) => {
            row.rest.as_deref() == Some(target)
                || row.effects.iter().any(|item| {
                    item.name == target || item.payload.as_deref() == Some(target)
                })
        }
        TypeAnnotation::Optional(inner) => type_annotation_has_effect_var(inner, target),
        TypeAnnotation::Existential {
            associated_types, ..
        } => associated_types
            .iter()
            .any(|(_, ty)| type_annotation_has_effect_var(ty, target)),
        TypeAnnotation::Named(_)
        | TypeAnnotation::Projection { .. }
        | TypeAnnotation::DimLiteral(_) => false,
    }
}

fn effect_var_is_constrained(effect_var: &str, params: &[Param]) -> bool {
    params.iter().any(|param| {
        param
            .annotation
            .as_ref()
            .is_some_and(|ann| type_annotation_has_effect_var(&ann.node, effect_var))
    })
}

fn ensure_effect_var_is_constrained(
    effect_var: &str,
    params: &[Param],
    span: Span,
) -> Result<(), Diagnostic> {
    if effect_var_is_constrained(effect_var, params) {
        Ok(())
    } else {
        Err(
            Diagnostic::error(
                Category::TypeMismatch,
                format!(
                    "effect variable `{effect_var}` is unconstrained; tie it to at least one function-typed parameter effect annotation"
                ),
            )
            .at(span_to_loc(span)),
        )
    }
}

/// Validate an optional declaration-level effect annotation against inferred effects.
///
/// Returns `Ok(())` when there is no annotation or when inferred effects satisfy it.
pub fn validate_declared_fn_effect(fn_decl: &FnDecl, inferred: Effects) -> Result<(), Diagnostic> {
    validate_declared_fn_effect_with_env(fn_decl, inferred, &TypeEnv::new())
}

/// Validate a declaration-level effect annotation against inferred effects and
/// the function body's effect-term model within a type environment.
///
/// This environment-aware variant is required for polymorphic contracts
/// (`-[e]>`) so the checker can verify that the body effect tracks `e`.
pub fn validate_declared_fn_effect_with_env(
    fn_decl: &FnDecl,
    inferred: Effects,
    env: &TypeEnv,
) -> Result<(), Diagnostic> {
    validate_declared_fn_effect_with_env_and_records(fn_decl, inferred, env, &RecordRegistry::new())
}

/// Validate an optional declaration-level effect annotation against an inferred row.
pub fn validate_declared_fn_effect_row(
    fn_decl: &FnDecl,
    inferred_row: &EffectRow,
) -> Result<(), Diagnostic> {
    validate_declared_fn_effect_row_with_env_and_records(
        fn_decl,
        inferred_row,
        &TypeEnv::new(),
        &RecordRegistry::new(),
    )
}

/// Validate a declaration-level effect annotation against an inferred row and
/// function-body effect model within a type environment.
pub fn validate_declared_fn_effect_row_with_env(
    fn_decl: &FnDecl,
    inferred_row: &EffectRow,
    env: &TypeEnv,
) -> Result<(), Diagnostic> {
    validate_declared_fn_effect_row_with_env_and_records(
        fn_decl,
        inferred_row,
        env,
        &RecordRegistry::new(),
    )
}

/// Record-aware variant of declared effect validation.
pub fn validate_declared_fn_effect_with_env_and_records(
    fn_decl: &FnDecl,
    inferred: Effects,
    env: &TypeEnv,
    records: &RecordRegistry,
) -> Result<(), Diagnostic> {
    let inferred_row = effect_row_from_effects(inferred);
    validate_declared_fn_effect_row_with_env_and_records(fn_decl, &inferred_row, env, records)
}

/// Record-aware variant of declared row validation.
pub fn validate_declared_fn_effect_row_with_env_and_records(
    fn_decl: &FnDecl,
    inferred_row: &EffectRow,
    env: &TypeEnv,
    records: &RecordRegistry,
) -> Result<(), Diagnostic> {
    let Some(ann) = &fn_decl.effect_annotation else {
        return Ok(());
    };
    let declared = parse_declared_effect(ann);
    if let Some(name) = effect_annotation_var_name(&declared) {
        ensure_effect_var_is_constrained(name, &fn_decl.params, ann.span)?;
        validate_declared_fn_effect_variable_contract(fn_decl, env, &fn_decl.name.node, name)?;
        return Ok(());
    }
    let Some(declared_row) = effect_annotation_to_compat_row(&declared, Some(records)) else {
        return Err(Diagnostic::error(
            Category::TypeMismatch,
            "invalid effect-row contract; expected row syntax like `-[IO, Fail AppError | e]>`",
        )
        .at(span_to_loc(ann.span)));
    };
    validate_effect_row_fail_cardinality(&declared_row, ann.span, "declaration")?;

    if let Err(row_err) = unify_effect_row_subsumption(inferred_row, &declared_row, ann.span) {
        let mut diag = Diagnostic::error(
            Category::TypeMismatch,
            format!(
                "declared effect `{}` is too weak; body requires `{}`",
                effect_annotation_label(&parse_declared_effect(ann)),
                inferred_row,
            ),
        )
        .at(span_to_loc(ann.span))
        .with_label(
            span_to_loc(ann.span),
            format!(
                "declared effect `{}` ({})",
                effect_annotation_label(&parse_declared_effect(ann)),
                declared_row,
            ),
        );
        if let Some(help) = row_err.help {
            diag = diag.with_help(help);
        }
        return Err(diag);
    }
    Ok(())
}
fn validate_declared_fn_effect_variable_contract(
    fn_decl: &FnDecl,
    env: &TypeEnv,
    fn_name: &str,
    effect_var_name: &str,
) -> Result<(), Diagnostic> {
    let mut trial_env = env.clone();
    // Recursive/self references use a conservative placeholder during validation.
    trial_env.set_function_effect_row(fn_name.to_string(), impure_effect_row());

    let mut effect_var_bindings = BTreeMap::new();
    let mut next_effect_var = 0u32;
    seed_function_param_effect_rows(
        &fn_decl.params,
        &mut trial_env,
        &mut effect_var_bindings,
        &mut next_effect_var,
    );

    let declared_var = *effect_var_bindings.get(effect_var_name).ok_or_else(|| {
        Diagnostic::error(
            Category::TypeMismatch,
            format!(
                "effect variable `{effect_var_name}` is unconstrained; tie it to at least one function-typed parameter effect annotation"
            ),
        )
        .at(span_to_loc(
            fn_decl
                .effect_annotation
                .as_ref()
                .map(|a| a.span)
                .unwrap_or(fn_decl.span),
        ))
    })?;

    let mut constraints = Vec::new();
    let root = infer_expr_effect_row(
        &fn_decl.body,
        &trial_env,
        &mut constraints,
        &mut next_effect_var,
    );

    let ann_span = fn_decl
        .effect_annotation
        .as_ref()
        .map(|a| a.span)
        .unwrap_or(fn_decl.span);
    for candidate in [pure_effect_row(), volatile_effect_row(), impure_effect_row()] {
        let mut scoped = constraints.clone();
        scoped.push(Constraint::RowEqual {
            expected: RowType::open(vec![], declared_var),
            actual: candidate.row.clone(),
            provenance: Provenance {
                span: ann_span,
                reason: Reason::TypeAscription,
            },
        });

        let mut unifier = Unifier::new();
        if let Err(err) = unifier.solve(scoped) {
            return Err(
                Diagnostic::error(
                    Category::TypeMismatch,
                    format!(
                        "declared effect `-[{effect_var_name}]>` on `{fn_name}` does not propagate through the body"
                    ),
                )
                .at(span_to_loc(ann_span))
                .with_help(format!(
                    "when `{effect_var_name}` is `{candidate}`, the body constraints are unsatisfiable; solver detail: {err}"
                )),
            );
        }

        let resolved_root = EffectRow {
            row: unifier.substitution.apply_row(&root.row),
        };
        if resolved_root != candidate {
            return Err(
                Diagnostic::error(
                    Category::TypeMismatch,
                    format!(
                        "declared effect `-[{effect_var_name}]>` on `{fn_name}` does not match body effect propagation"
                    ),
                )
                .at(span_to_loc(ann_span))
                .with_help(format!(
                    "when `{effect_var_name}` is `{candidate}`, the body resolves to `{resolved_root}` instead"
                )),
            );
        }
    }

    Ok(())
}

/// Validate that an impl method's inferred effect satisfies a trait method contract.
pub fn validate_trait_method_impl_effect(
    trait_name: &str,
    method_name: &str,
    method_span: Span,
    inferred: Effects,
    required: Effects,
) -> Result<(), Diagnostic> {
    validate_trait_method_impl_effect_row(
        trait_name,
        method_name,
        method_span,
        inferred,
        &effect_row_from_effects(required),
    )
}

fn validate_trait_method_impl_effect_row(
    trait_name: &str,
    method_name: &str,
    method_span: Span,
    inferred: Effects,
    required: &EffectRow,
) -> Result<(), Diagnostic> {
    validate_effect_row_fail_cardinality(required, method_span, "trait contract")?;
    let inferred_row = effect_row_from_effects(inferred);
    if let Err(row_err) = unify_effect_row_subsumption(&inferred_row, required, method_span) {
        let mut diag = Diagnostic::error(
            Category::TypeMismatch,
            format!(
                "impl method `{method_name}` has effect `{inferred_row}`, but trait `{trait_name}` requires `{required}`"
            ),
        )
        .at(span_to_loc(method_span))
        .with_label(
            span_to_loc(method_span),
            format!("method effect `{inferred_row}` exceeds trait contract `{required}`"),
        );
        if let Some(help) = row_err.help {
            diag = diag.with_help(help);
        }
        return Err(diag);
    }
    Ok(())
}

/// Validate that an impl method satisfies a trait method effect contract.
///
/// Concrete trait contracts (`pure|volatile|impure`) are enforced against the
/// inferred impl-method effects. Polymorphic contracts (`-[e]>`) require the
/// impl method to declare a constrained effect variable as well.
pub fn validate_trait_method_impl_contract(
    trait_name: &str,
    method_name: &str,
    method_span: Span,
    inferred: Effects,
    impl_declared_effect: Option<&kea_ast::Spanned<kea_ast::EffectAnnotation>>,
    impl_params: &[Param],
    required: Option<&kea_ast::EffectAnnotation>,
) -> Result<(), Diagnostic> {
    let Some(required) = required else {
        return Ok(());
    };

    if let Some(required_row) = effect_annotation_to_compat_row(required, None) {
        return validate_trait_method_impl_effect_row(
            trait_name,
            method_name,
            method_span,
            inferred,
            &required_row,
        );
    }

    let Some(required_var) = effect_annotation_var_name(required) else {
        return Err(Diagnostic::error(
            Category::TypeMismatch,
            format!(
                "trait method contract `{}` is not yet supported for impl checking; use a concrete level or `-[e]>`",
                effect_annotation_label(required)
            ),
        )
        .at(span_to_loc(method_span)));
    };

    let Some(impl_ann) = impl_declared_effect else {
        return Err(
            Diagnostic::error(
                Category::TypeMismatch,
                format!(
                    "impl method `{method_name}` must declare an effect variable (`-[e]>`) to satisfy polymorphic trait method contract `{required_var}` on trait `{trait_name}`"
                ),
            )
            .at(span_to_loc(method_span)),
        );
    };
    if let Some(name) = effect_annotation_var_name(&impl_ann.node) {
        return ensure_effect_var_is_constrained(name, impl_params, impl_ann.span);
    }
    Err(Diagnostic::error(
        Category::TypeMismatch,
        format!(
            "impl method `{method_name}` must declare an effect variable (`-[e]>`) to satisfy polymorphic trait method contract `{required_var}` on trait `{trait_name}`"
        ),
    )
    .at(span_to_loc(impl_ann.span)))
}

/// Environment-aware trait method contract validation.
///
/// For concrete trait contracts, behaves like [`validate_trait_method_impl_contract`].
/// For polymorphic contracts (`-[e]>`), additionally requires the impl body to
/// propagate its declared effect variable exactly across the effect lattice.
pub fn validate_trait_method_impl_contract_with_env(
    trait_name: &str,
    method: &FnDecl,
    inferred: Effects,
    env: &TypeEnv,
    required: Option<&kea_ast::EffectAnnotation>,
) -> Result<(), Diagnostic> {
    let Some(required) = required else {
        return Ok(());
    };

    if let Some(required_row) = effect_annotation_to_compat_row(required, None) {
        return validate_trait_method_impl_effect_row(
            trait_name,
            &method.name.node,
            method.name.span,
            inferred,
            &required_row,
        );
    }

    let Some(required_var) = effect_annotation_var_name(required) else {
        return Err(Diagnostic::error(
            Category::TypeMismatch,
            format!(
                "trait method contract `{}` is not yet supported for impl checking; use a concrete level or `-[e]>`",
                effect_annotation_label(required)
            ),
        )
        .at(span_to_loc(method.name.span)));
    };

    let Some(impl_ann) = method.effect_annotation.as_ref() else {
        return Err(
            Diagnostic::error(
                Category::TypeMismatch,
                format!(
                    "impl method `{}` must declare an effect variable (`-[e]>`) to satisfy polymorphic trait method contract `{required_var}` on trait `{trait_name}`",
                    method.name.node
                ),
            )
            .at(span_to_loc(method.name.span)),
        );
    };

    if let Some(name) = effect_annotation_var_name(&impl_ann.node) {
        ensure_effect_var_is_constrained(name, &method.params, impl_ann.span)?;
        return validate_declared_fn_effect_variable_contract(method, env, &method.name.node, name);
    }
    Err(Diagnostic::error(
        Category::TypeMismatch,
        format!(
            "impl method `{}` must declare an effect variable (`-[e]>`) to satisfy polymorphic trait method contract `{required_var}` on trait `{trait_name}`",
            method.name.node
        ),
    )
    .at(span_to_loc(impl_ann.span)))
}

/// Infer effects for an expression.
///
/// This tracks evaluation effects (purity/volatility) bottom-up so function
/// declarations can be classified without manual annotation.
pub fn infer_expr_effects(expr: &Expr, env: &TypeEnv) -> Effects {
    let mut constraints = Vec::new();
    let mut next_effect_var = 0u32;
    let root = infer_expr_effect_row(expr, env, &mut constraints, &mut next_effect_var);
    let mut unifier = Unifier::new();
    if unifier.solve(constraints).is_err() {
        Effects::impure()
    } else {
        let resolved = EffectRow {
            row: unifier.substitution.apply_row(&root.row),
        };
        classify_effect_row(&resolved)
    }
}

fn infer_expr_effect_row(
    expr: &Expr,
    env: &TypeEnv,
    constraints: &mut Vec<Constraint>,
    next_effect_var: &mut u32,
) -> EffectRow {
    match &expr.node {
        ExprKind::Lit(_)
        | ExprKind::Var(_)
        | ExprKind::Lambda { .. }
        | ExprKind::None
        | ExprKind::Atom(_)
        | ExprKind::Wildcard => pure_effect_row(),

        ExprKind::Tuple(elems) | ExprKind::List(elems) => {
            let mut terms = Vec::with_capacity(elems.len());
            for elem in elems {
                terms.push(infer_expr_effect_row(
                    elem,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::Range { start, end, .. } => join_effect_rows_many(
            vec![
                infer_expr_effect_row(start, env, constraints, next_effect_var),
                infer_expr_effect_row(end, env, constraints, next_effect_var),
            ],
            constraints,
            next_effect_var,
        ),

        ExprKind::Let { value, .. } => {
            infer_expr_effect_row(value, env, constraints, next_effect_var)
        }

        ExprKind::Handle {
            expr: handled,
            clauses,
            then_clause,
        } => {
            let handled_effects = infer_expr_effect_row(handled, env, constraints, next_effect_var);
            let mut clause_terms = Vec::with_capacity(clauses.len());
            for clause in clauses {
                clause_terms.push(infer_expr_effect_row(
                    &clause.body,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            let clause_effects = join_effect_rows_many(clause_terms, constraints, next_effect_var);

            let then_effects = then_clause.as_ref().map(|then_expr| {
                join_effect_rows(
                    infer_expr_effect_row(then_expr, env, constraints, next_effect_var),
                    infer_callable_value_effect_row(then_expr, env, constraints, next_effect_var),
                    constraints,
                    next_effect_var,
                )
            });

            let body_effects = if let Some(then_effects) = then_effects {
                join_effect_rows(clause_effects, then_effects, constraints, next_effect_var)
            } else {
                clause_effects
            };

            let Some(first_clause) = clauses.first() else {
                return join_effect_rows(handled_effects, body_effects, constraints, next_effect_var);
            };

            let handled_label = Label::new(first_clause.effect.node.clone());
            let rest = fresh_effect_var(next_effect_var);
            constraints.push(Constraint::RowEqual {
                expected: RowType::open(vec![(handled_label, Type::Unit)], rest),
                actual: handled_effects.row,
                provenance: Provenance {
                    span: expr.span,
                    reason: Reason::TypeAscription,
                },
            });

            let passthrough = EffectRow::open(vec![], rest);
            join_effect_rows(passthrough, body_effects, constraints, next_effect_var)
        }

        ExprKind::Resume { value } => {
            infer_expr_effect_row(value, env, constraints, next_effect_var)
        }

        ExprKind::Call { func, args } => {
            let mut terms = Vec::with_capacity(args.len() + 2);
            let mut arg_eval_terms = Vec::with_capacity(args.len());
            for arg in args {
                arg_eval_terms.push(infer_expr_effect_row(
                    &arg.value,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            terms.extend(arg_eval_terms.iter().cloned());
            terms.push(infer_expr_effect_row(
                func,
                env,
                constraints,
                next_effect_var,
            ));
            let call_effect = infer_call_effect_row(func, args, env, constraints, next_effect_var);
            terms.push(call_effect);
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut terms = vec![
                infer_expr_effect_row(condition, env, constraints, next_effect_var),
                infer_expr_effect_row(then_branch, env, constraints, next_effect_var),
            ];
            if let Some(otherwise) = else_branch {
                terms.push(infer_expr_effect_row(
                    otherwise,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::Case { scrutinee, arms } => {
            let mut terms = vec![infer_expr_effect_row(
                scrutinee,
                env,
                constraints,
                next_effect_var,
            )];
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    terms.push(infer_expr_effect_row(
                        guard,
                        env,
                        constraints,
                        next_effect_var,
                    ));
                }
                terms.push(infer_expr_effect_row(
                    &arm.body,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::Cond { arms } => {
            let mut terms = Vec::with_capacity(arms.len() * 2);
            for arm in arms {
                terms.push(infer_expr_effect_row(
                    &arm.condition,
                    env,
                    constraints,
                    next_effect_var,
                ));
                terms.push(infer_expr_effect_row(
                    &arm.body,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::BinaryOp { left, right, .. } => {
            let left_term = infer_expr_effect_row(left, env, constraints, next_effect_var);
            let right_term = infer_expr_effect_row(right, env, constraints, next_effect_var);
            join_effect_rows(left_term, right_term, constraints, next_effect_var)
        }

        ExprKind::WhenGuard { body, condition } => {
            let cond_term = infer_expr_effect_row(condition, env, constraints, next_effect_var);
            let body_term = infer_expr_effect_row(body, env, constraints, next_effect_var);
            join_effect_rows(cond_term, body_term, constraints, next_effect_var)
        }

        ExprKind::UnaryOp { operand, .. } | ExprKind::As { expr: operand, .. } => {
            infer_expr_effect_row(operand, env, constraints, next_effect_var)
        }

        ExprKind::Record { fields, spread, .. } | ExprKind::AnonRecord { fields, spread } => {
            let mut terms = Vec::with_capacity(fields.len() + usize::from(spread.is_some()));
            for (_, value) in fields {
                terms.push(infer_expr_effect_row(
                    value,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            if let Some(spread_expr) = spread {
                terms.push(infer_expr_effect_row(
                    spread_expr,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::FieldAccess { expr, .. } => {
            infer_expr_effect_row(expr, env, constraints, next_effect_var)
        }

        ExprKind::Block(exprs) => {
            let mut terms = Vec::new();
            let mut block_env = env.clone();
            let mut idx = 0usize;
            while idx < exprs.len() {
                let current = &exprs[idx];
                if let ExprKind::Use(use_expr) = &current.node {
                    if let Ok(lowered) = lower_use_chain_to_bind(exprs, idx) {
                        terms.push(infer_expr_effect_row(
                            &lowered,
                            &block_env,
                            constraints,
                            next_effect_var,
                        ));
                    } else {
                        terms.push(infer_expr_effect_row(
                            &use_expr.rhs,
                            &block_env,
                            constraints,
                            next_effect_var,
                        ));
                    }
                    break;
                }
                if let ExprKind::Let { pattern, value, .. } = &current.node {
                    let value_term =
                        infer_expr_effect_row(value, &block_env, constraints, next_effect_var);
                    terms.push(value_term);
                    let (callable_term, callable_signature) = match &value.node {
                        ExprKind::Var(source_name) => (
                            block_env.function_effect_row(source_name),
                            block_env.function_effect_signature(source_name).cloned(),
                        ),
                        ExprKind::FieldAccess { expr, field } => {
                            if let ExprKind::Var(module) = &expr.node {
                                (
                                    block_env.resolve_qualified_effect_row(module, &field.node),
                                    block_env
                                        .resolve_qualified_effect_signature(module, &field.node)
                                        .cloned(),
                                )
                            } else {
                                (None, None)
                            }
                        }
                        ExprKind::Lambda { params, body, .. } => {
                            let signature = infer_lambda_effect_signature(
                                params,
                                body,
                                &block_env,
                                constraints,
                                next_effect_var,
                            );
                            (Some(signature.effect_row.clone()), Some(signature))
                        }
                        ExprKind::Call { func, .. } => {
                            callable_effect_metadata_from_call(func, &block_env, next_effect_var)
                        }
                        _ => (None, None),
                    };
                    bind_let_pattern_effect_metadata(
                        pattern,
                        callable_term,
                        callable_signature,
                        &mut block_env,
                    );
                    idx += 1;
                    continue;
                }
                terms.push(infer_expr_effect_row(
                    current,
                    &block_env,
                    constraints,
                    next_effect_var,
                ));
                idx += 1;
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::Use(use_expr) => {
            infer_expr_effect_row(&use_expr.rhs, env, constraints, next_effect_var)
        }

        ExprKind::Constructor { args, .. } => {
            let mut terms = Vec::with_capacity(args.len());
            for arg in args {
                terms.push(infer_expr_effect_row(
                    &arg.value,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::StringInterp(parts) => {
            let mut terms = Vec::new();
            for part in parts {
                if let kea_ast::StringInterpPart::Expr(inner) = part {
                    terms.push(infer_expr_effect_row(
                        inner,
                        env,
                        constraints,
                        next_effect_var,
                    ));
                }
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::MapLiteral(pairs) => {
            let mut terms = Vec::with_capacity(pairs.len() * 2);
            for (k, v) in pairs {
                terms.push(infer_expr_effect_row(k, env, constraints, next_effect_var));
                terms.push(infer_expr_effect_row(v, env, constraints, next_effect_var));
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::For(for_expr) => {
            let mut terms = Vec::with_capacity(for_expr.clauses.len() + 1);
            for clause in &for_expr.clauses {
                let term = match clause {
                    ForClause::Generator { source, .. } => {
                        infer_expr_effect_row(source, env, constraints, next_effect_var)
                    }
                    ForClause::Guard(guard) => {
                        infer_expr_effect_row(guard, env, constraints, next_effect_var)
                    }
                };
                terms.push(term);
            }
            terms.push(infer_expr_effect_row(
                &for_expr.body,
                env,
                constraints,
                next_effect_var,
            ));
            join_effect_rows_many(terms, constraints, next_effect_var)
        }

        ExprKind::Spawn { value, config } => {
            let mut terms = vec![
                impure_effect_row(),
                infer_expr_effect_row(value, env, constraints, next_effect_var),
            ];
            if let Some(cfg) = config {
                for entry in [
                    cfg.mailbox_size.as_ref(),
                    cfg.supervision.as_ref(),
                    cfg.max_restarts.as_ref(),
                    cfg.call_timeout.as_ref(),
                ]
                .into_iter()
                .flatten()
                {
                    terms.push(infer_expr_effect_row(
                        entry,
                        env,
                        constraints,
                        next_effect_var,
                    ));
                }
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }
        ExprKind::Await { expr, .. } => join_effect_rows(
            impure_effect_row(),
            infer_expr_effect_row(expr, env, constraints, next_effect_var),
            constraints,
            next_effect_var,
        ),
        ExprKind::StreamBlock { body, .. } => join_effect_rows(
            impure_effect_row(),
            infer_expr_effect_row(body, env, constraints, next_effect_var),
            constraints,
            next_effect_var,
        ),
        ExprKind::Yield { value } => join_effect_rows(
            impure_effect_row(),
            infer_expr_effect_row(value, env, constraints, next_effect_var),
            constraints,
            next_effect_var,
        ),
        ExprKind::YieldFrom { source } => join_effect_rows(
            impure_effect_row(),
            infer_expr_effect_row(source, env, constraints, next_effect_var),
            constraints,
            next_effect_var,
        ),
        ExprKind::ActorSend { actor, args, .. } => {
            let mut terms = Vec::with_capacity(args.len() + 2);
            terms.push(impure_effect_row());
            terms.push(infer_expr_effect_row(
                actor,
                env,
                constraints,
                next_effect_var,
            ));
            for arg in args {
                terms.push(infer_expr_effect_row(
                    arg,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }
        ExprKind::ActorCall { actor, args, .. } => {
            let mut terms = Vec::with_capacity(args.len() + 2);
            terms.push(impure_effect_row());
            terms.push(infer_expr_effect_row(
                actor,
                env,
                constraints,
                next_effect_var,
            ));
            for arg in args {
                terms.push(infer_expr_effect_row(
                    arg,
                    env,
                    constraints,
                    next_effect_var,
                ));
            }
            join_effect_rows_many(terms, constraints, next_effect_var)
        }
        ExprKind::ControlSend { actor, signal } => join_effect_rows_many(
            [
                impure_effect_row(),
                infer_expr_effect_row(actor, env, constraints, next_effect_var),
                infer_expr_effect_row(signal, env, constraints, next_effect_var),
            ],
            constraints,
            next_effect_var,
        ),
    }
}

#[derive(Debug, Clone, Copy)]
struct ForInferContext {
    span: Span,
}

#[derive(Debug, Clone, Copy)]
enum ForSourceKind {
    List,
    Option,
    Result,
    Stream,
}

#[derive(Debug, Clone)]
struct ForChainDescriptor {
    constructor: String,
    args: Vec<Type>,
    hole_index: usize,
}

fn push_ambiguous_trait_impl_error(unifier: &mut Unifier, trait_name: &str, ty: &Type, span: Span) {
    unifier.push_error(
        Diagnostic::error(
            Category::TraitBound,
            format!("ambiguous impl resolution for trait `{trait_name}` on type `{ty}`"),
        )
        .at(span_to_loc(span))
        .with_help(
            "add a more specific type annotation or associated-type constraint to disambiguate",
        ),
    );
}

fn solve_trait_impl_with_diag(
    traits: &TraitRegistry,
    unifier: &mut Unifier,
    trait_name: &str,
    ty: &Type,
    span: Span,
) -> SolveOutcome {
    match traits.solve_goal(&TraitGoal::Implements {
        trait_name: trait_name.to_string(),
        ty: ty.clone(),
    }) {
        SolveOutcome::Ambiguous(candidates) => {
            push_ambiguous_trait_impl_error(unifier, trait_name, ty, span);
            SolveOutcome::Ambiguous(candidates)
        }
        other => other,
    }
}

fn impl_nomatch_detail(reasons: &[MismatchReason]) -> Option<String> {
    reasons.iter().find_map(|reason| match reason {
        MismatchReason::UnknownTrait { trait_name } => {
            Some(format!("trait `{trait_name}` is not registered"))
        }
        MismatchReason::NoImplForConstructor {
            trait_name,
            type_constructor,
        } => Some(format!(
            "no `{trait_name}` impl found for type constructor `{type_constructor}`"
        )),
        MismatchReason::FundepConflict { dependency } => Some(format!(
            "functional dependency conflict while solving `{dependency}`"
        )),
        MismatchReason::ParamBoundUnsatisfied {
            param,
            bound_trait,
            ty,
        } => Some(format!(
            "bound `{param}: {bound_trait}` is unsatisfied for `{ty}`"
        )),
        MismatchReason::SupertraitUnsatisfied { supertrait, ty } => Some(format!(
            "required supertrait `{supertrait}` is unsatisfied for `{ty}`"
        )),
        _ => None,
    })
}

fn solve_projection_eq_with_diag(
    traits: &TraitRegistry,
    unifier: &mut Unifier,
    base_trait: &str,
    base_ty: &Type,
    assoc: &str,
    rhs: &Type,
    span: Span,
) -> SolveOutcome {
    match traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: base_trait.to_string(),
        base_ty: base_ty.clone(),
        assoc: assoc.to_string(),
        rhs: rhs.clone(),
    }) {
        SolveOutcome::Unique(candidate) => {
            if let Some(found) = candidate.associated_types.get(assoc) {
                constrain_type_eq(
                    unifier,
                    rhs,
                    found,
                    &Provenance {
                        span,
                        reason: Reason::TraitBound {
                            trait_name: base_trait.to_string(),
                        },
                    },
                );
            }
            SolveOutcome::Unique(candidate)
        }
        SolveOutcome::Ambiguous(candidates) => {
            push_ambiguous_trait_impl_error(unifier, base_trait, base_ty, span);
            SolveOutcome::Ambiguous(candidates)
        }
        SolveOutcome::NoMatch(reasons) => SolveOutcome::NoMatch(reasons),
    }
}

fn projection_nomatch_detail(reasons: &[MismatchReason]) -> Option<String> {
    reasons.iter().find_map(|reason| match reason {
        MismatchReason::UnknownTrait { trait_name } => {
            Some(format!("trait `{trait_name}` is not registered"))
        }
        MismatchReason::NotATypeConstructor { ty } => Some(format!(
            "`{ty}` is not a trait-dispatchable type constructor"
        )),
        MismatchReason::FundepConflict { dependency } => Some(format!(
            "functional dependency conflict while solving `{dependency}`"
        )),
        MismatchReason::AssocTypeMismatch {
            assoc,
            expected,
            found,
        } => Some(format!(
            "associated type `{assoc}` mismatch: expected `{expected}`, found `{found}`"
        )),
        MismatchReason::MissingAssociatedType { assoc } => {
            Some(format!("missing required associated type `{assoc}`"))
        }
        MismatchReason::NoImplForConstructor {
            trait_name,
            type_constructor,
        } => Some(format!(
            "no `{trait_name}` impl found for type constructor `{type_constructor}`"
        )),
        _ => None,
    })
}

fn resolve_for_chain_descriptor(
    source_ty: &Type,
    source_span: Span,
    traits: &TraitRegistry,
    unifier: &mut Unifier,
) -> Option<ForChainDescriptor> {
    let resolved = unifier.substitution.apply(source_ty);
    let Some((constructor, args)) = type_constructor_for_trait(&resolved) else {
        unifier.push_error(
            Diagnostic::error(
                Category::TypeError,
                format!("cannot iterate over `{resolved}`"),
            )
            .at(span_to_loc(source_span))
            .with_help("`for` works with comprehensible container types like List, Option, Result, and Stream"),
        );
        return None;
    };

    let candidate =
        match solve_trait_impl_with_diag(traits, unifier, "Comprehensible", &resolved, source_span)
        {
            SolveOutcome::Unique(candidate) => candidate,
            SolveOutcome::Ambiguous(_) => return None,
            SolveOutcome::NoMatch(reasons) => {
                let detail = impl_nomatch_detail(&reasons)
                    .map(|d| format!("; {d}"))
                    .unwrap_or_default();
                unifier.push_error(
                    Diagnostic::error(
                        Category::TypeError,
                        format!("cannot iterate over `{resolved}`"),
                    )
                    .at(span_to_loc(source_span))
                    .with_help(format!(
                        "this type does not implement Comprehensible{detail}"
                    )),
                );
                return None;
            }
        };
    let impl_info = candidate.impl_index.and_then(|idx| traits.impls.get(idx));
    let hole_index = if let Some(imp) = impl_info {
        if let Some(idx) = imp.type_params.iter().position(|p| p == "_") {
            idx
        } else if args.len() == 1 {
            0
        } else if imp.type_params.len() < args.len() {
            // Positional partial application rule: first unfilled slot from the left.
            imp.type_params.len()
        } else {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!("cannot determine comprehension hole for `{constructor}`"),
                )
                .at(span_to_loc(source_span)),
            );
            return None;
        }
    } else if args.len() == 1 {
        0
    } else {
        unifier.push_error(
            Diagnostic::error(
                Category::TypeError,
                format!("cannot determine comprehension hole for `{constructor}`"),
            )
            .at(span_to_loc(source_span)),
        );
        return None;
    };

    if hole_index >= args.len() {
        unifier.push_error(
            Diagnostic::error(
                Category::TypeError,
                format!("cannot determine comprehension hole for `{constructor}`"),
            )
            .at(span_to_loc(source_span)),
        );
        return None;
    }

    Some(ForChainDescriptor {
        constructor,
        args,
        hole_index,
    })
}

fn infer_for_generator_item_type_hkt(
    desc: &ForChainDescriptor,
    source_ty: &Type,
    source_span: Span,
    unifier: &mut Unifier,
) -> Type {
    let prov = Provenance {
        span: source_span,
        reason: Reason::FunctionArg { param_index: 0 },
    };
    let resolved = unifier.substitution.apply(source_ty);
    let Some((source_ctor, source_args)) = type_constructor_for_trait(&resolved) else {
        unifier.push_error(
            Diagnostic::error(
                Category::TypeError,
                format!("cannot iterate over `{resolved}`"),
            )
            .at(span_to_loc(source_span))
            .with_help("for-comprehension sources must be comprehensible container values"),
        );
        return unifier.fresh_type();
    };

    if source_ctor == desc.constructor {
        if source_args.len() != desc.args.len() {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "all generators in a for-comprehension must have matching constructor arity; expected {}, got {}",
                        desc.args.len(),
                        source_args.len()
                    ),
                )
                .at(span_to_loc(source_span)),
            );
            return unifier.fresh_type();
        }

        for (idx, (expected, actual)) in desc.args.iter().zip(source_args.iter()).enumerate() {
            if idx == desc.hole_index {
                continue;
            }
            constrain_type_eq(unifier, actual, expected, &prov);
        }

        return source_args
            .get(desc.hole_index)
            .cloned()
            .unwrap_or_else(|| unifier.fresh_type());
    }

    unifier.push_error(
        Diagnostic::error(
            Category::TypeError,
            format!(
                "all generators in a for-comprehension must share one container constructor; got `{}` and `{}`",
                desc.constructor, source_ctor
            ),
        )
        .at(span_to_loc(source_span)),
    );
    unifier.fresh_type()
}

fn mk_var(name: &str, span: Span) -> Expr {
    kea_ast::Spanned::new(ExprKind::Var(name.to_string()), span)
}

fn mk_call(name: &str, args: Vec<Expr>, span: Span) -> Expr {
    kea_ast::Spanned::new(
        ExprKind::Call {
            func: Box::new(mk_var(name, span)),
            args: args
                .into_iter()
                .map(|value| Argument { label: None, value })
                .collect(),
        },
        span,
    )
}

fn mk_string_lit(value: impl Into<String>, span: Span) -> Expr {
    kea_ast::Spanned::new(ExprKind::Lit(Lit::String(value.into())), span)
}

fn mk_qualified_call(receiver: &str, method: &str, args: Vec<Expr>, span: Span) -> Expr {
    kea_ast::Spanned::new(
        ExprKind::Call {
            func: Box::new(kea_ast::Spanned::new(
                ExprKind::FieldAccess {
                    expr: Box::new(mk_var(receiver, span)),
                    field: kea_ast::Spanned::new(method.to_string(), span),
                },
                span,
            )),
            args: args
                .into_iter()
                .map(|value| Argument { label: None, value })
                .collect(),
        },
        span,
    )
}

fn mk_trait_call(trait_name: &str, method: &str, args: Vec<Expr>, span: Span) -> Expr {
    mk_qualified_call(trait_name, method, args, span)
}

fn mk_lambda(param: &str, body: Expr, span: Span) -> Expr {
    kea_ast::Spanned::new(
        ExprKind::Lambda {
            params: vec![kea_ast::Param {
                label: ParamLabel::Implicit,
                pattern: kea_ast::Spanned::new(PatternKind::Var(param.to_string()), span),
                annotation: None,
                default: None,
            }],
            body: Box::new(body),
            return_annotation: None,
        },
        span,
    )
}

fn mk_list(items: Vec<Expr>, span: Span) -> Expr {
    kea_ast::Spanned::new(ExprKind::List(items), span)
}

fn mk_if(condition: Expr, then_branch: Expr, else_branch: Expr, span: Span) -> Expr {
    kea_ast::Spanned::new(
        ExprKind::If {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch: Some(Box::new(else_branch)),
        },
        span,
    )
}

fn mk_case(scrutinee: Expr, arms: Vec<kea_ast::CaseArm>, span: Span) -> Expr {
    kea_ast::Spanned::new(
        ExprKind::Case {
            scrutinee: Box::new(scrutinee),
            arms,
        },
        span,
    )
}

fn mk_wildcard_pattern(span: Span) -> kea_ast::Pattern {
    kea_ast::Spanned::new(PatternKind::Wildcard, span)
}

fn block_tail_expr(exprs: &[Expr], start_index: usize, fallback_span: Span) -> Expr {
    let tail = &exprs[start_index..];
    match tail {
        [] => kea_ast::Spanned::new(ExprKind::Lit(Lit::Unit), fallback_span),
        [single] => single.clone(),
        _ => {
            let start = tail.first().map(|e| e.span).unwrap_or(fallback_span);
            let end = tail.last().map(|e| e.span).unwrap_or(fallback_span);
            kea_ast::Spanned::new(ExprKind::Block(tail.to_vec()), start.merge(end))
        }
    }
}

#[derive(Debug, Clone)]
struct UseStep {
    pattern: kea_ast::Pattern,
    source: Expr,
}

fn collect_use_chain(
    exprs: &[Expr],
    start_index: usize,
) -> Result<(Vec<UseStep>, Expr, Span), &'static str> {
    let mut steps = Vec::new();
    let mut idx = start_index;
    let chain_span = exprs
        .get(start_index)
        .map(|e| e.span)
        .unwrap_or(Span::synthetic());

    while let Some(expr) = exprs.get(idx) {
        let ExprKind::Use(use_expr) = &expr.node else {
            break;
        };
        let pattern = use_expr
            .pattern
            .clone()
            .unwrap_or_else(|| mk_wildcard_pattern(expr.span));
        steps.push(UseStep {
            pattern,
            source: *use_expr.rhs.clone(),
        });
        idx += 1;
    }

    if steps.is_empty() {
        return Err("internal error lowering use chain to bind");
    }
    if idx >= exprs.len() {
        return Err("`use` must be followed by a continuation expression");
    }

    let continuation = block_tail_expr(exprs, idx, chain_span);
    Ok((steps, continuation, chain_span))
}

fn pattern_is_irrefutable(pattern: &kea_ast::Pattern) -> bool {
    match &pattern.node {
        PatternKind::Wildcard | PatternKind::Var(_) => true,
        PatternKind::Tuple(items) => items.iter().all(pattern_is_irrefutable),
        PatternKind::Record { fields, .. } | PatternKind::AnonRecord { fields, .. } => fields
            .iter()
            .all(|(_, field_pattern)| pattern_is_irrefutable(field_pattern)),
        PatternKind::Lit(_) | PatternKind::Constructor { .. } => false,
        PatternKind::Or(_) => false, // or-patterns are refutable
        PatternKind::As { pattern, .. } => pattern_is_irrefutable(pattern),
        // List patterns are refutable — [] doesn't match [1,2], [h,..t] doesn't match []
        PatternKind::List { .. } => false,
    }
}

fn lower_use_chain_to_bind(exprs: &[Expr], start_index: usize) -> Result<Expr, &'static str> {
    let (steps, continuation, chain_span) = collect_use_chain(exprs, start_index)?;
    let resolved: Vec<ResolvedUseStep> = steps
        .into_iter()
        .map(|step| ResolvedUseStep {
            step,
            dispatch: UseDispatch::Bind,
            from_coercion: None,
        })
        .collect();
    Ok(lower_use_chain_with_dispatch(
        &resolved,
        continuation,
        chain_span,
    ))
}

#[derive(Debug, Clone)]
struct UseChainDescriptor {
    constructor: String,
    args: Vec<Type>,
    hole_index: usize,
}

#[derive(Debug, Clone, Copy)]
enum UseDispatch {
    Bind,
    Resource,
}

#[derive(Debug, Clone)]
struct FromCoercion {
    target_type: String,
    source_type: String,
}

#[derive(Debug, Clone)]
struct ResolvedUseStep {
    step: UseStep,
    dispatch: UseDispatch,
    from_coercion: Option<FromCoercion>,
}

fn wrap_result_source_with_from_coercion(
    source: Expr,
    coercion: &FromCoercion,
    span: Span,
    idx: usize,
) -> Expr {
    let err_tmp = format!("__use_from_err_{idx}");
    mk_call(
        "result_map_err",
        vec![
            source,
            mk_lambda(
                &err_tmp,
                mk_call(
                    "result_from_coerce_internal",
                    vec![
                        mk_var(&err_tmp, span),
                        mk_string_lit(coercion.target_type.clone(), span),
                        mk_string_lit(coercion.source_type.clone(), span),
                    ],
                    span,
                ),
                span,
            ),
        ],
        span,
    )
}

fn lower_use_chain_with_dispatch(
    steps: &[ResolvedUseStep],
    continuation: Expr,
    chain_span: Span,
) -> Expr {
    let mut lowered = continuation;

    for (idx, resolved) in steps.iter().enumerate().rev() {
        let step = &resolved.step;
        let tmp = format!("__use_item_{idx}");
        let body = mk_case(
            mk_var(&tmp, step.source.span),
            vec![kea_ast::CaseArm {
                pattern: step.pattern.clone(),
                guard: None,
                body: lowered,
            }],
            step.source.span,
        );
        let trait_name = match resolved.dispatch {
            UseDispatch::Bind => "Bind",
            UseDispatch::Resource => "Resource",
        };
        let method_name = match resolved.dispatch {
            UseDispatch::Bind => "bind",
            UseDispatch::Resource => "with",
        };
        let source_expr = match (&resolved.dispatch, &resolved.from_coercion) {
            (UseDispatch::Bind, Some(coercion)) => wrap_result_source_with_from_coercion(
                step.source.clone(),
                coercion,
                step.source.span,
                idx,
            ),
            _ => step.source.clone(),
        };
        lowered = mk_trait_call(
            trait_name,
            method_name,
            vec![source_expr, mk_lambda(&tmp, body, step.source.span)],
            step.source.span,
        );
    }

    kea_ast::Spanned::new(lowered.node, chain_span)
}

fn resolve_bind_use_chain_descriptor(
    source_ty: &Type,
    source_span: Span,
    traits: &TraitRegistry,
    unifier: &mut Unifier,
) -> Option<UseChainDescriptor> {
    let resolved = unifier.substitution.apply(source_ty);
    let Some((constructor, args)) = type_constructor_for_trait(&resolved) else {
        unifier.push_error(
            Diagnostic::error(
                Category::TypeError,
                format!("cannot use `use` with `{resolved}`"),
            )
            .at(span_to_loc(source_span))
            .with_help(
                "`use` works with container types like Result, Option, List, and Stream; use `let` for plain values",
            ),
        );
        return None;
    };

    let candidate = match solve_trait_impl_with_diag(
        traits,
        unifier,
        "Bind",
        &resolved,
        source_span,
    ) {
        SolveOutcome::Unique(candidate) => candidate,
        SolveOutcome::Ambiguous(_) => return None,
        SolveOutcome::NoMatch(reasons) => {
            let mut help = if args.is_empty() {
                "`use` works with container types like Result, Option, List, and Stream; use `let` for plain values"
            } else {
                "this type does not implement Bind"
            }
            .to_string();
            if let Some(detail) = impl_nomatch_detail(&reasons) {
                help = format!("{help}; {detail}");
            }
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!("cannot use `use` with `{resolved}`"),
                )
                .at(span_to_loc(source_span))
                .with_help(help),
            );
            return None;
        }
    };
    let impl_info = candidate.impl_index.and_then(|idx| traits.impls.get(idx));
    let hole_index = if let Some(imp) = impl_info {
        if let Some(idx) = imp.type_params.iter().position(|p| p == "_") {
            idx
        } else if args.len() == 1 {
            0
        } else if imp.type_params.len() < args.len() {
            // Positional partial application rule: first unfilled slot from the left.
            imp.type_params.len()
        } else {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!("cannot determine bind hole for `{constructor}`"),
                )
                .at(span_to_loc(source_span)),
            );
            return None;
        }
    } else if args.len() == 1 {
        0
    } else {
        unifier.push_error(
            Diagnostic::error(
                Category::TypeError,
                format!("cannot determine bind hole for `{constructor}`"),
            )
            .at(span_to_loc(source_span)),
        );
        return None;
    };

    if hole_index >= args.len() {
        unifier.push_error(
            Diagnostic::error(
                Category::TypeError,
                format!("cannot determine bind hole for `{constructor}`"),
            )
            .at(span_to_loc(source_span)),
        );
        return None;
    }

    Some(UseChainDescriptor {
        constructor,
        args,
        hole_index,
    })
}

fn resolve_resource_value_type(
    source_ty: &Type,
    source_span: Span,
    traits: &TraitRegistry,
    unifier: &mut Unifier,
) -> Result<Option<Type>, ()> {
    let resolved = unifier.substitution.apply(source_ty);
    match solve_trait_impl_with_diag(traits, unifier, "Resource", &resolved, source_span) {
        SolveOutcome::Unique(candidate) => Ok(candidate.associated_types.get("Value").cloned()),
        SolveOutcome::Ambiguous(_) => Err(()),
        SolveOutcome::NoMatch(_) => Ok(None),
    }
}

fn has_from_impl_for(
    target_ty: &Type,
    source_ty: &Type,
    traits: &TraitRegistry,
    source_span: Span,
    unifier: &mut Unifier,
) -> (Option<FromCoercion>, Option<String>) {
    let Some((target_ctor, _target_args)) = type_constructor_for_trait(target_ty) else {
        return (None, None);
    };
    let Some((source_ctor, _source_args)) = type_constructor_for_trait(source_ty) else {
        return (None, None);
    };
    match solve_projection_eq_with_diag(
        traits,
        unifier,
        "From",
        target_ty,
        "Source",
        source_ty,
        source_span,
    ) {
        SolveOutcome::Unique(_) => (
            Some(FromCoercion {
                target_type: target_ctor,
                source_type: source_ctor,
            }),
            None,
        ),
        SolveOutcome::Ambiguous(_) => (None, None),
        SolveOutcome::NoMatch(reasons) => (None, projection_nomatch_detail(&reasons)),
    }
}

fn infer_use_chain_expr(
    exprs: &[Expr],
    start_index: usize,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Type {
    let (steps, continuation, chain_span) = match collect_use_chain(exprs, start_index) {
        Ok(parts) => parts,
        Err(message) => {
            let span = exprs
                .get(start_index)
                .map(|e| e.span)
                .unwrap_or(Span::synthetic());
            unifier
                .push_error(Diagnostic::error(Category::TypeError, message).at(span_to_loc(span)));
            return unifier.fresh_type();
        }
    };

    let Some(first_step) = steps.first() else {
        unifier.push_error(
            Diagnostic::error(Category::TypeError, "internal error inferring use chain")
                .at(span_to_loc(chain_span)),
        );
        return unifier.fresh_type();
    };

    let first_source_ty =
        infer_expr_bidir(&first_step.source, env, unifier, records, traits, sum_types);
    let first_resource = match resolve_resource_value_type(
        &first_source_ty,
        first_step.source.span,
        traits,
        unifier,
    ) {
        Ok(Some(_)) => true,
        Ok(None) => false,
        Err(()) => return unifier.fresh_type(),
    };
    let mut chain_bind_desc = if first_resource {
        None
    } else {
        resolve_bind_use_chain_descriptor(&first_source_ty, first_step.source.span, traits, unifier)
    };
    if !first_resource && chain_bind_desc.is_none() {
        return unifier.fresh_type();
    }

    let mut pushed_scopes = 0usize;
    let mut resolved_steps: Vec<ResolvedUseStep> = Vec::with_capacity(steps.len());
    for step in &steps {
        if !pattern_is_irrefutable(&step.pattern) {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    "`use` requires an irrefutable pattern",
                )
                .at(span_to_loc(step.pattern.span))
                .with_help("use variables, `_`, tuples, or record destructuring; use `case` for constructor/literal matching"),
            );
        }

        let source_ty = infer_expr_bidir(&step.source, env, unifier, records, traits, sum_types);

        match resolve_resource_value_type(&source_ty, step.source.span, traits, unifier) {
            Ok(Some(value_ty)) => {
                env.push_scope();
                pushed_scopes += 1;
                infer_pattern(&step.pattern, &value_ty, env, unifier, records, sum_types);
                resolved_steps.push(ResolvedUseStep {
                    step: step.clone(),
                    dispatch: UseDispatch::Resource,
                    from_coercion: None,
                });
                continue;
            }
            Ok(None) => {}
            Err(()) => return unifier.fresh_type(),
        }

        let resolved_source = unifier.substitution.apply(&source_ty);
        let Some((_source_ctor, source_args)) = type_constructor_for_trait(&resolved_source) else {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!("cannot use `use` with `{resolved_source}`"),
                )
                .at(span_to_loc(step.source.span))
                .with_help(
                    "`use` works with container types like Result, Option, List, and Stream; use `let` for plain values",
                ),
            );
            env.push_scope();
            pushed_scopes += 1;
            infer_pattern(
                &step.pattern,
                &unifier.fresh_type(),
                env,
                unifier,
                records,
                sum_types,
            );
            continue;
        };

        let Some(desc) =
            resolve_bind_use_chain_descriptor(&source_ty, step.source.span, traits, unifier)
        else {
            env.push_scope();
            pushed_scopes += 1;
            infer_pattern(
                &step.pattern,
                &unifier.fresh_type(),
                env,
                unifier,
                records,
                sum_types,
            );
            continue;
        };

        let mut step_from_coercion: Option<FromCoercion> = None;
        if let Some(chain_desc) = &chain_bind_desc {
            if desc.constructor != chain_desc.constructor {
                if chain_desc.constructor == "Result" && desc.constructor == "Option" {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::TypeError,
                            "cannot use `use` with Option in a Result context",
                        )
                        .at(span_to_loc(step.source.span))
                        .with_help("convert Option explicitly, e.g. `opt |> Option.ok_or(MyError.NotFound)`"),
                    );
                } else {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::TypeError,
                            format!(
                                "all values in a use chain must share one container constructor; got `{}` and `{}`",
                                chain_desc.constructor, desc.constructor
                            ),
                        )
                        .at(span_to_loc(step.source.span)),
                    );
                }
                env.push_scope();
                pushed_scopes += 1;
                infer_pattern(
                    &step.pattern,
                    &unifier.fresh_type(),
                    env,
                    unifier,
                    records,
                    sum_types,
                );
                continue;
            }

            if desc.args.len() != chain_desc.args.len() {
                unifier.push_error(
                    Diagnostic::error(
                        Category::TypeError,
                        format!(
                            "all values in a use chain must have matching constructor arity; expected {}, got {}",
                            chain_desc.args.len(),
                            desc.args.len()
                        ),
                    )
                    .at(span_to_loc(step.source.span)),
                );
                env.push_scope();
                pushed_scopes += 1;
                infer_pattern(
                    &step.pattern,
                    &unifier.fresh_type(),
                    env,
                    unifier,
                    records,
                    sum_types,
                );
                continue;
            }

            for (idx, (expected, actual)) in
                chain_desc.args.iter().zip(desc.args.iter()).enumerate()
            {
                if idx == chain_desc.hole_index {
                    continue;
                }
                let expected_resolved = unifier.substitution.apply(expected);
                let actual_resolved = unifier.substitution.apply(actual);
                if chain_desc.constructor == "Result"
                    && !matches!(expected_resolved, Type::Var(_))
                    && !matches!(actual_resolved, Type::Var(_))
                    && expected_resolved != actual_resolved
                {
                    let (coercion, coercion_detail) = has_from_impl_for(
                        &expected_resolved,
                        &actual_resolved,
                        traits,
                        step.source.span,
                        unifier,
                    );
                    if let Some(coercion) = coercion {
                        if idx == chain_desc.hole_index {
                            // never set coercion on success-position mismatch.
                        } else {
                            step_from_coercion = Some(coercion);
                            continue;
                        }
                    } else {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::TypeError,
                                "mismatched error types in `use` chain",
                            )
                            .at(span_to_loc(step.source.span))
                            .with_help(format!(
                                "all Result values in a use chain must share one error type; got `{actual_resolved}` and `{expected_resolved}`{}",
                                coercion_detail
                                    .map(|detail| format!("; {detail}"))
                                    .unwrap_or_default()
                            )),
                        );
                    }
                }
                constrain_type_eq(
                    unifier,
                    actual,
                    expected,
                    &Provenance {
                        span: step.source.span,
                        reason: Reason::FunctionArg { param_index: idx },
                    },
                );
            }
        } else {
            chain_bind_desc = Some(desc.clone());
        }

        let item_ty = source_args
            .get(desc.hole_index.min(source_args.len().saturating_sub(1)))
            .cloned()
            .unwrap_or_else(|| unifier.fresh_type());
        env.push_scope();
        pushed_scopes += 1;
        infer_pattern(&step.pattern, &item_ty, env, unifier, records, sum_types);
        resolved_steps.push(ResolvedUseStep {
            step: step.clone(),
            dispatch: UseDispatch::Bind,
            from_coercion: step_from_coercion,
        });
    }

    let mut body_ty = infer_expr_bidir(&continuation, env, unifier, records, traits, sum_types);
    for _ in 0..pushed_scopes {
        env.pop_scope();
    }

    if let Some(desc) = &chain_bind_desc {
        let item_ty = unifier.fresh_type();
        let mut expected_args = desc.args.clone();
        if desc.hole_index < expected_args.len() {
            expected_args[desc.hole_index] = item_ty;
        }
        let expected_cont = rebuild_type(&desc.constructor, &expected_args).unwrap_or_else(|| {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "cannot rebuild result type for use chain constructor `{}`",
                        desc.constructor
                    ),
                )
                .at(span_to_loc(chain_span)),
            );
            unifier.fresh_type()
        });
        constrain_type_eq(
            unifier,
            &body_ty,
            &expected_cont,
            &Provenance {
                span: chain_span,
                reason: Reason::FunctionArg { param_index: 1 },
            },
        );
        body_ty = expected_cont;
    }

    let lowered = lower_use_chain_with_dispatch(&resolved_steps, continuation, chain_span);
    if let Some(head) = exprs.get(start_index) {
        unifier
            .type_annotations
            .use_desugared
            .insert(head.span, lowered);
    }

    body_ty
}

fn mk_var_pattern(name: &str, span: Span) -> kea_ast::Pattern {
    kea_ast::Spanned::new(PatternKind::Var(name.to_string()), span)
}

fn mk_ctor_pattern(name: &str, args: Vec<kea_ast::Pattern>, span: Span) -> kea_ast::Pattern {
    kea_ast::Spanned::new(
        PatternKind::Constructor {
            name: name.to_string(),
            qualifier: None,
            args: args
                .into_iter()
                .map(|pattern| kea_ast::ConstructorFieldPattern {
                    name: None,
                    pattern,
                })
                .collect(),
            rest: false,
        },
        span,
    )
}

fn lower_source_to_list(
    source: &Expr,
    kind: ForSourceKind,
    span: Span,
    tmp_counter: &mut usize,
) -> Expr {
    match kind {
        ForSourceKind::List => source.clone(),
        ForSourceKind::Stream => mk_call("stream_to_list", vec![source.clone()], span),
        ForSourceKind::Option => {
            let tmp = format!("__for_src_{}", *tmp_counter);
            *tmp_counter += 1;
            mk_case(
                source.clone(),
                vec![
                    kea_ast::CaseArm {
                        pattern: mk_ctor_pattern("Some", vec![mk_var_pattern(&tmp, span)], span),
                        guard: None,
                        body: mk_list(vec![mk_var(&tmp, span)], span),
                    },
                    kea_ast::CaseArm {
                        pattern: mk_ctor_pattern("None", vec![], span),
                        guard: None,
                        body: mk_list(vec![], span),
                    },
                ],
                span,
            )
        }
        ForSourceKind::Result => {
            let ok_tmp = format!("__for_src_{}", *tmp_counter);
            *tmp_counter += 1;
            mk_case(
                source.clone(),
                vec![
                    kea_ast::CaseArm {
                        pattern: mk_ctor_pattern("Ok", vec![mk_var_pattern(&ok_tmp, span)], span),
                        guard: None,
                        body: mk_list(vec![mk_var(&ok_tmp, span)], span),
                    },
                    kea_ast::CaseArm {
                        pattern: mk_ctor_pattern("Err", vec![mk_wildcard_pattern(span)], span),
                        guard: None,
                        body: mk_list(vec![], span),
                    },
                ],
                span,
            )
        }
    }
}

fn constructor_is_list_like(constructor: &str) -> bool {
    matches!(constructor, "List" | "Stream")
}

fn classify_for_source_kind(source_ty: &Type, unifier: &mut Unifier) -> ForSourceKind {
    let resolved = unifier.substitution.apply(source_ty);
    let Some((ctor, _args)) = type_constructor_for_trait(&resolved) else {
        return ForSourceKind::List;
    };
    match ctor.as_str() {
        "List" => ForSourceKind::List,
        "Option" => ForSourceKind::Option,
        "Result" => ForSourceKind::Result,
        "Stream" => ForSourceKind::Stream,
        _ => ForSourceKind::List,
    }
}

#[derive(Debug, Clone)]
struct SimpleForGenerator {
    clause_index: usize,
    binding: String,
    source: Expr,
    guards: Vec<Expr>,
}

fn simple_for_generators(clauses: &[ForClause]) -> Option<Vec<SimpleForGenerator>> {
    let mut generators = Vec::new();
    let mut current: Option<SimpleForGenerator> = None;

    for (idx, clause) in clauses.iter().enumerate() {
        match clause {
            ForClause::Generator { pattern, source } => {
                if let Some(generator) = current.take() {
                    generators.push(generator);
                }
                let binding = match &pattern.node {
                    PatternKind::Var(name) => name.clone(),
                    PatternKind::Wildcard => format!("__for_ignored_{idx}"),
                    _ => return None,
                };
                current = Some(SimpleForGenerator {
                    clause_index: idx,
                    binding,
                    source: *source.clone(),
                    guards: Vec::new(),
                });
            }
            ForClause::Guard(guard) => {
                let current = current.as_mut()?;
                current.guards.push(*guard.clone());
            }
        }
    }

    if let Some(generator) = current {
        generators.push(generator);
    }

    if generators.is_empty() {
        None
    } else {
        Some(generators)
    }
}

fn apply_simple_list_like_guards(generator: &SimpleForGenerator, source: Expr, span: Span) -> Expr {
    generator.guards.iter().fold(source, |acc, guard| {
        mk_trait_call(
            "Comprehensible",
            "filter",
            vec![acc, mk_lambda(&generator.binding, guard.clone(), span)],
            span,
        )
    })
}

fn lower_generator_source_for_chain(
    generator: &SimpleForGenerator,
    desc: &ForChainDescriptor,
    source_kinds: &BTreeMap<usize, ForSourceKind>,
    span: Span,
    tmp_counter: &mut usize,
) -> Expr {
    if !constructor_is_list_like(&desc.constructor) {
        return generator.source.clone();
    }
    lower_source_to_list(
        &generator.source,
        source_kinds
            .get(&generator.clause_index)
            .copied()
            .unwrap_or(ForSourceKind::List),
        span,
        tmp_counter,
    )
}

fn lower_for_simple_generators(
    generators: &[SimpleForGenerator],
    index: usize,
    body: &Expr,
    desc: &ForChainDescriptor,
    source_kinds: &BTreeMap<usize, ForSourceKind>,
    span: Span,
    tmp_counter: &mut usize,
) -> Expr {
    let generator = &generators[index];
    let lowered_source =
        lower_generator_source_for_chain(generator, desc, source_kinds, span, tmp_counter);
    let filtered_source = apply_simple_list_like_guards(generator, lowered_source, span);

    if index + 1 == generators.len() {
        mk_trait_call(
            "Comprehensible",
            "map",
            vec![
                filtered_source,
                mk_lambda(&generator.binding, body.clone(), span),
            ],
            span,
        )
    } else {
        let rest = lower_for_simple_generators(
            generators,
            index + 1,
            body,
            desc,
            source_kinds,
            span,
            tmp_counter,
        );
        mk_trait_call(
            "Bind",
            "bind",
            vec![filtered_source, mk_lambda(&generator.binding, rest, span)],
            span,
        )
    }
}

fn is_independent_simple_generator(lhs_binding: &str, rhs: &SimpleForGenerator) -> bool {
    if !rhs.guards.is_empty() {
        return false;
    }
    !free_vars(&rhs.source).contains(lhs_binding)
}

fn lower_for_simple_two_generator_applicative(
    first: &SimpleForGenerator,
    second: &SimpleForGenerator,
    body: &Expr,
    desc: &ForChainDescriptor,
    source_kinds: &BTreeMap<usize, ForSourceKind>,
    span: Span,
    tmp_counter: &mut usize,
) -> Expr {
    let first_source = apply_simple_list_like_guards(
        first,
        lower_generator_source_for_chain(first, desc, source_kinds, span, tmp_counter),
        span,
    );
    let second_source =
        lower_generator_source_for_chain(second, desc, source_kinds, span, tmp_counter);
    let curried = mk_lambda(&second.binding, body.clone(), span);
    let lifted = mk_trait_call(
        "Comprehensible",
        "map",
        vec![first_source, mk_lambda(&first.binding, curried, span)],
        span,
    );
    mk_trait_call("Applicative", "apply", vec![lifted, second_source], span)
}

fn lower_for_list_like_clauses(
    clauses: &[ForClause],
    clause_index_offset: usize,
    body: &Expr,
    source_kinds: &BTreeMap<usize, ForSourceKind>,
    span: Span,
    tmp_counter: &mut usize,
) -> Expr {
    let Some((first, rest)) = clauses.split_first() else {
        return mk_list(vec![body.clone()], span);
    };

    match first {
        ForClause::Guard(guard) => mk_if(
            *guard.clone(),
            lower_for_list_like_clauses(
                rest,
                clause_index_offset + 1,
                body,
                source_kinds,
                span,
                tmp_counter,
            ),
            mk_list(vec![], span),
            span,
        ),
        ForClause::Generator { pattern, source } => {
            let item = format!("__for_item_{}", *tmp_counter);
            *tmp_counter += 1;
            let lowered_source = lower_source_to_list(
                source,
                *source_kinds
                    .get(&clause_index_offset)
                    .unwrap_or(&ForSourceKind::List),
                span,
                tmp_counter,
            );
            let rest_expr = lower_for_list_like_clauses(
                rest,
                clause_index_offset + 1,
                body,
                source_kinds,
                span,
                tmp_counter,
            );
            let case_expr = mk_case(
                mk_var(&item, span),
                vec![
                    kea_ast::CaseArm {
                        pattern: pattern.clone(),
                        guard: None,
                        body: rest_expr,
                    },
                    kea_ast::CaseArm {
                        pattern: mk_wildcard_pattern(span),
                        guard: None,
                        body: mk_list(vec![], span),
                    },
                ],
                span,
            );
            mk_trait_call(
                "Bind",
                "bind",
                vec![lowered_source, mk_lambda(&item, case_expr, span)],
                span,
            )
        }
    }
}

fn has_remaining_generator(clauses: &[ForClause]) -> bool {
    clauses
        .iter()
        .any(|clause| matches!(clause, ForClause::Generator { .. }))
}

fn lower_for_non_list_like_clauses(
    clauses: &[ForClause],
    body: &Expr,
    span: Span,
    tmp_counter: &mut usize,
) -> Expr {
    let Some((first, rest)) = clauses.split_first() else {
        return body.clone();
    };

    match first {
        ForClause::Guard(_guard) => lower_for_non_list_like_clauses(rest, body, span, tmp_counter),
        ForClause::Generator { pattern, source } => {
            let item = format!("__for_item_{}", *tmp_counter);
            *tmp_counter += 1;
            let rest_expr = lower_for_non_list_like_clauses(rest, body, span, tmp_counter);
            let case_expr = mk_case(
                mk_var(&item, span),
                vec![kea_ast::CaseArm {
                    pattern: pattern.clone(),
                    guard: None,
                    body: rest_expr,
                }],
                span,
            );
            if has_remaining_generator(rest) {
                mk_trait_call(
                    "Bind",
                    "bind",
                    vec![*source.clone(), mk_lambda(&item, case_expr, span)],
                    span,
                )
            } else {
                mk_trait_call(
                    "Comprehensible",
                    "map",
                    vec![*source.clone(), mk_lambda(&item, case_expr, span)],
                    span,
                )
            }
        }
    }
}

fn apply_for_into_lowering(
    lowered: Expr,
    chain_constructor: &str,
    into: Option<&kea_ast::Spanned<TypeAnnotation>>,
    span: Span,
) -> Expr {
    if !constructor_is_list_like(chain_constructor) {
        return lowered;
    }
    let base_list = lowered;

    match into.map(|ann| &ann.node) {
        None if chain_constructor == "Stream" => mk_call("stream_from_list", vec![base_list], span),
        None => base_list,
        Some(TypeAnnotation::Named(name)) if name == "List" => base_list,
        Some(TypeAnnotation::Named(name)) if name == "Set" => {
            mk_call("set_from_list", vec![base_list], span)
        }
        Some(TypeAnnotation::Named(name)) if name == "Map" => {
            mk_call("map_from_pairs", vec![base_list], span)
        }
        Some(TypeAnnotation::Named(name)) if name == "Stream" => {
            mk_call("stream_from_list", vec![base_list], span)
        }
        _ => base_list,
    }
}

fn desugar_for_expr_hkt(
    for_expr: &ForExpr,
    desc: &ForChainDescriptor,
    span: Span,
    source_kinds: &BTreeMap<usize, ForSourceKind>,
    allow_applicative: bool,
) -> Expr {
    let mut tmp_counter = 0usize;
    let lowered = if let Some(generators) = simple_for_generators(&for_expr.clauses) {
        if allow_applicative
            && generators.len() == 2
            && is_independent_simple_generator(&generators[0].binding, &generators[1])
        {
            lower_for_simple_two_generator_applicative(
                &generators[0],
                &generators[1],
                &for_expr.body,
                desc,
                source_kinds,
                span,
                &mut tmp_counter,
            )
        } else {
            lower_for_simple_generators(
                &generators,
                0,
                &for_expr.body,
                desc,
                source_kinds,
                span,
                &mut tmp_counter,
            )
        }
    } else if constructor_is_list_like(&desc.constructor) {
        lower_for_list_like_clauses(
            &for_expr.clauses,
            0,
            &for_expr.body,
            source_kinds,
            span,
            &mut tmp_counter,
        )
    } else {
        lower_for_non_list_like_clauses(&for_expr.clauses, &for_expr.body, span, &mut tmp_counter)
    };

    apply_for_into_lowering(
        lowered,
        &desc.constructor,
        for_expr.into_type.as_ref(),
        span,
    )
}

fn infer_for_expr(
    for_expr: &ForExpr,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
    ctx: ForInferContext,
) -> Type {
    let Some(ForClause::Generator {
        source: first_source,
        ..
    }) = for_expr.clauses.first()
    else {
        unifier.push_error(
            Diagnostic::error(
                Category::Syntax,
                "for expression must start with a generator (`pattern in source`)".to_string(),
            )
            .at(span_to_loc(ctx.span)),
        );
        return unifier.fresh_type();
    };

    let first_source_ty = infer_expr_bidir(first_source, env, unifier, records, traits, sum_types);
    let Some(desc) =
        resolve_for_chain_descriptor(&first_source_ty, first_source.span, traits, unifier)
    else {
        return unifier.fresh_type();
    };
    let list_like_chain = constructor_is_list_like(&desc.constructor);

    let mut pushed_scopes = 0usize;
    let mut source_kinds: BTreeMap<usize, ForSourceKind> = BTreeMap::new();

    for (idx, clause) in for_expr.clauses.iter().enumerate() {
        match clause {
            ForClause::Generator { pattern, source } => {
                let source_ty = infer_expr_bidir(source, env, unifier, records, traits, sum_types);
                if list_like_chain {
                    source_kinds.insert(idx, classify_for_source_kind(&source_ty, unifier));
                }
                let item_ty =
                    infer_for_generator_item_type_hkt(&desc, &source_ty, source.span, unifier);
                env.push_scope();
                pushed_scopes += 1;
                infer_pattern(pattern, &item_ty, env, unifier, records, sum_types);
            }
            ForClause::Guard(guard) => {
                let guard_ty = infer_expr_bidir(guard, env, unifier, records, traits, sum_types);
                let resolved_guard = unifier.substitution.apply(&guard_ty);
                if !matches!(resolved_guard, Type::Bool | Type::Var(_)) {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::TypeError,
                            format!("guard expression must be Bool, got `{resolved_guard}`"),
                        )
                        .at(span_to_loc(guard.span))
                        .with_help("guards filter elements; use a boolean predicate like `x > 0`"),
                    );
                }
                constrain_type_eq(
                    unifier,
                    &guard_ty,
                    &Type::Bool,
                    &Provenance {
                        span: guard.span,
                        reason: Reason::CaseArms,
                    },
                );
            }
        }
    }

    let body_ty = infer_expr_bidir(&for_expr.body, env, unifier, records, traits, sum_types);
    for _ in 0..pushed_scopes {
        env.pop_scope();
    }

    let mut out_args = desc.args.clone();
    if desc.hole_index < out_args.len() {
        out_args[desc.hole_index] = body_ty.clone();
    }
    let mut result_ty = rebuild_type(&desc.constructor, &out_args).unwrap_or_else(|| {
        unifier.push_error(
            Diagnostic::error(
                Category::TypeError,
                format!(
                    "cannot rebuild comprehension result type for constructor `{}`",
                    desc.constructor
                ),
            )
            .at(span_to_loc(ctx.span)),
        );
        unifier.fresh_type()
    });

    if let Some(into_ann) = &for_expr.into_type {
        if !list_like_chain {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "`into` is not supported for `{}` comprehensions; use List or Stream sources",
                        desc.constructor
                    ),
                )
                .at(span_to_loc(into_ann.span)),
            );
            return result_ty;
        }

        result_ty = match &into_ann.node {
            TypeAnnotation::Named(name) if name == "List" => Type::List(Box::new(body_ty.clone())),
            TypeAnnotation::Named(name) if name == "Set" => {
                let resolved_elem = unifier.substitution.apply(&body_ty);
                if traits.lookup_trait("Hashable").is_some()
                    && !matches!(resolved_elem, Type::Var(_))
                {
                    match solve_trait_impl_with_diag(
                        traits,
                        unifier,
                        "Hashable",
                        &resolved_elem,
                        into_ann.span,
                    ) {
                        SolveOutcome::Unique(_) => {}
                        SolveOutcome::Ambiguous(_) => {}
                        SolveOutcome::NoMatch(_) => {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::TraitBound,
                                    format!(
                                        "`into Set` requires element type to implement Hashable, got `{resolved_elem}`"
                                    ),
                                )
                                .at(span_to_loc(into_ann.span)),
                            );
                        }
                    }
                }
                Type::Set(Box::new(body_ty.clone()))
            }
            TypeAnnotation::Named(name) if name == "Map" => {
                let resolved_body = unifier.substitution.apply(&body_ty);
                if !matches!(resolved_body, Type::Tuple(ref elems) if elems.len() == 2)
                    && !matches!(resolved_body, Type::Var(_))
                {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::TypeError,
                            format!(
                                "cannot collect into Map — body must yield 2-tuples, got `{resolved_body}`"
                            ),
                        )
                        .at(span_to_loc(into_ann.span))
                        .with_help("to collect into Map, yield `(key, value)` tuples in the body"),
                    );
                }
                let k = unifier.fresh_type();
                let v = unifier.fresh_type();
                constrain_type_eq(
                    unifier,
                    &body_ty,
                    &Type::Tuple(vec![k.clone(), v.clone()]),
                    &Provenance {
                        span: into_ann.span,
                        reason: Reason::FunctionArg { param_index: 0 },
                    },
                );
                Type::Map(Box::new(k), Box::new(v))
            }
            TypeAnnotation::Named(name) if name == "Stream" => {
                Type::Stream(Box::new(body_ty.clone()))
            }
            other => {
                unifier.push_error(
                    Diagnostic::error(
                        Category::TypeError,
                        format!(
                            "unsupported `into` target `{}` (use List, Set, Map, or Stream)",
                            annotation_display(other)
                        ),
                    )
                    .at(span_to_loc(into_ann.span)),
                );
                result_ty
            }
        };
    }

    let applicative_target = rebuild_type(&desc.constructor, &desc.args).unwrap_or_else(|| {
        Type::App(
            Box::new(Type::Constructor {
                name: desc.constructor.clone(),
                fixed_args: Vec::new(),
                arity: desc.args.len(),
            }),
            desc.args.clone(),
        )
    });
    let has_applicative = match solve_trait_impl_with_diag(
        traits,
        unifier,
        "Applicative",
        &applicative_target,
        ctx.span,
    ) {
        SolveOutcome::Unique(_) => true,
        SolveOutcome::NoMatch(_) => false,
        SolveOutcome::Ambiguous(_) => false,
    };
    let desugared = desugar_for_expr_hkt(for_expr, &desc, ctx.span, &source_kinds, has_applicative);
    unifier
        .type_annotations
        .for_desugared
        .insert(ctx.span, desugared);

    result_ty
}

fn note_existential_pack_sites(
    unifier: &mut Unifier,
    call_span: Span,
    func_ty: &Type,
    arg_types: &[Type],
) {
    let resolved_func = unifier.substitution.apply(func_ty);
    let Type::Function(ft) = resolved_func else {
        return;
    };

    let mut sites = Vec::new();
    for (i, param_ty) in ft.params.iter().enumerate() {
        if i >= arg_types.len() {
            break;
        }
        if let Type::Existential {
            bounds,
            associated_types,
        } = param_ty
        {
            let concrete_type = unifier.substitution.apply(&arg_types[i]);
            if matches!(concrete_type, Type::Var(_)) {
                continue;
            }
            sites.push(ExistentialPackSite {
                arg_index: i,
                concrete_type,
                bounds: bounds.clone(),
                associated_types: associated_types.clone(),
            });
        }
    }

    if !sites.is_empty() {
        unifier
            .type_annotations
            .existential_packs
            .insert(call_span, sites);
    }
}

fn enforce_existential_bounds_for_arg(
    bounds: &[String],
    arg_ty: &Type,
    arg_span: Span,
    unifier: &mut Unifier,
) {
    let resolved_arg = unifier.substitution.apply(arg_ty);
    for bound in bounds {
        let prov = Provenance {
            span: arg_span,
            reason: Reason::TraitBound {
                trait_name: bound.clone(),
            },
        };
        constrain_trait_obligation(unifier, &resolved_arg, bound, &prov);
    }
}

fn arg_bind_error_message(err: &ArgBindError) -> String {
    match &err.kind {
        ArgBindErrorKind::UnknownLabel { label } => {
            format!("unknown argument label `{label}`")
        }
        ArgBindErrorKind::DuplicateLabel { label } => {
            format!("duplicate argument label `{label}`")
        }
        ArgBindErrorKind::MissingRequired { label, index } => {
            if let Some(label) = label {
                format!("missing required argument `{label}`")
            } else {
                format!(
                    "missing required positional argument at position {}",
                    index + 1
                )
            }
        }
        ArgBindErrorKind::TooManyArguments { expected, got } => {
            format!("too many arguments: expected {expected}, got {got}")
        }
        ArgBindErrorKind::PositionalAfterLabeled => {
            "positional arguments must come before labeled arguments".to_string()
        }
    }
}

fn push_arg_bind_diag(unifier: &mut Unifier, call_span: Span, err: ArgBindError) {
    let mut diag = Diagnostic::error(Category::ArityMismatch, arg_bind_error_message(&err))
        .at(span_to_loc(err.span.unwrap_or(call_span)));
    if let ArgBindErrorKind::UnknownLabel { .. } = err.kind {
        diag = diag.with_help(
            "use one of the function's declared labels, or pass the argument positionally",
        );
    }
    if let ArgBindErrorKind::PositionalAfterLabeled = err.kind {
        diag = diag
            .with_help("once a labeled argument appears, all remaining arguments must be labeled");
    }
    unifier.push_error(diag);
}

fn resolve_call_signature<'a>(func: &Expr, env: &'a TypeEnv) -> Option<&'a FnSignature> {
    match &func.node {
        ExprKind::Var(name) => env.function_signature(name),
        ExprKind::FieldAccess { expr, field } => {
            if let ExprKind::Var(module_name) = &expr.node {
                env.resolve_qualified_function_signature(module_name, &field.node)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn resolve_bound_call_args(
    func: &Expr,
    args: &[Argument],
    call_span: Span,
    env: &TypeEnv,
    unifier: &mut Unifier,
) -> (Option<FnSignature>, Vec<BoundArg>) {
    let signature = resolve_call_signature(func, env).cloned();
    let has_labels = args.iter().any(|arg| arg.label.is_some());
    let fallback = args
        .iter()
        .map(|arg| BoundArg::Provided(arg.value.clone()))
        .collect::<Vec<_>>();

    let Some(signature) = signature else {
        if has_labels {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeMismatch,
                    "labeled arguments require a direct named function call; first-class function values must be called positionally",
                )
                .at(span_to_loc(call_span)),
            );
        }
        return (None, fallback);
    };

    match bind_args(&signature, args) {
        Ok(bound) => (Some(signature), bound),
        Err(err) => {
            push_arg_bind_diag(unifier, call_span, err);
            (Some(signature), fallback)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn infer_bound_args_with_param_contracts(
    bound_args: &[BoundArg],
    signature: Option<&FnSignature>,
    params: Option<&[Type]>,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Vec<Type> {
    let mut default_env = env.clone();
    default_env.push_scope();
    let mut arg_types = Vec::with_capacity(bound_args.len());

    for (idx, bound_arg) in bound_args.iter().enumerate() {
        let maybe_param = params.and_then(|param_tys| param_tys.get(idx));
        let arg_ty = match (bound_arg, maybe_param) {
            (BoundArg::Provided(expr), Some(param_ty)) => infer_and_enforce_param_contract(
                expr, param_ty, idx, env, unifier, records, traits, sum_types,
            ),
            (BoundArg::Default(expr), Some(param_ty)) => infer_and_enforce_param_contract(
                expr,
                param_ty,
                idx,
                &mut default_env,
                unifier,
                records,
                traits,
                sum_types,
            ),
            (BoundArg::Provided(expr), None) => {
                infer_expr_bidir(expr, env, unifier, records, traits, sum_types)
            }
            (BoundArg::Default(expr), None) => {
                infer_expr_bidir(expr, &mut default_env, unifier, records, traits, sum_types)
            }
        };

        if let Some(param_name) = signature
            .and_then(|sig| sig.params.get(idx))
            .and_then(|param| param.name.as_ref())
        {
            default_env.bind(param_name.clone(), TypeScheme::mono(arg_ty.clone()));
        }
        arg_types.push(arg_ty);
    }

    arg_types
}

fn instantiate_callable_type_for_call(func_ty: &Type, unifier: &mut Unifier, span: Span) -> Type {
    let resolved = unifier.substitution.apply(func_ty);
    match resolved {
        Type::Forall(scheme) => instantiate_with_span(&scheme, unifier, span),
        other => other,
    }
}

fn params_for_call_unification(callable_ty: &Type, arg_types: &[Type]) -> Vec<Type> {
    let Type::Function(ft) = callable_ty else {
        return arg_types.to_vec();
    };
    if ft.params.len() != arg_types.len() {
        return arg_types.to_vec();
    }

    ft.params
        .iter()
        .zip(arg_types.iter())
        .map(|(param_ty, arg_ty)| match param_ty {
            Type::Existential { .. } | Type::Forall(_) => param_ty.clone(),
            _ => arg_ty.clone(),
        })
        .collect()
}

fn poly_scheme_from_env_scheme(scheme: &TypeScheme) -> Option<TypeScheme> {
    if scheme.is_mono() {
        None
    } else {
        Some(scheme.clone())
    }
}

fn poly_scheme_from_argument_expr(
    arg_expr: &Expr,
    arg_ty: &Type,
    env: &TypeEnv,
    unifier: &mut Unifier,
) -> Option<TypeScheme> {
    let resolved_arg = unifier.substitution.apply(arg_ty);
    if let Type::Forall(scheme) = resolved_arg {
        return Some(*scheme);
    }

    match &arg_expr.node {
        ExprKind::Var(name) => env.lookup(name).and_then(poly_scheme_from_env_scheme),
        ExprKind::FieldAccess { expr, field } => {
            if let ExprKind::Var(module_name) = &expr.node
                && env.lookup(module_name).is_none()
                && looks_like_module_name(module_name)
            {
                return env
                    .resolve_qualified(module_name, &field.node)
                    .and_then(poly_scheme_from_env_scheme);
            }
            None
        }
        _ => None,
    }
}

fn skolemize_poly_scheme(scheme: &TypeScheme) -> Type {
    let mut subst = Substitution::new();
    for (i, tv) in scheme.type_vars.iter().enumerate() {
        subst.bind_type(
            *tv,
            Type::Opaque {
                name: format!("__rank2_skolem_{i}"),
                params: vec![],
            },
        );
    }
    subst.apply(&scheme.ty)
}

fn argument_satisfies_rank2_param(
    arg_expr: &Expr,
    arg_ty: &Type,
    expected_scheme: &TypeScheme,
    env: &TypeEnv,
    unifier: &mut Unifier,
    param_index: usize,
) -> bool {
    let Some(actual_scheme) = poly_scheme_from_argument_expr(arg_expr, arg_ty, env, unifier) else {
        return false;
    };

    let mut probe = unifier.clone();
    let expected_ty = skolemize_poly_scheme(expected_scheme);
    let actual_ty = instantiate(&actual_scheme, &mut probe);
    let constraints = vec![Constraint::TypeEqual {
        expected: expected_ty,
        actual: actual_ty,
        provenance: Provenance {
            span: arg_expr.span,
            reason: Reason::FunctionArg { param_index },
        },
    }];
    probe.constraints_satisfiable(constraints)
}

fn push_rank2_argument_mismatch_diag(
    unifier: &mut Unifier,
    arg_expr: &Expr,
    arg_index: usize,
    expected_scheme: &TypeScheme,
) {
    unifier.push_error(
        Diagnostic::error(
            Category::TypeMismatch,
            format!(
                "argument {} is not polymorphic enough: expected `{}`",
                arg_index + 1,
                Type::Forall(Box::new(expected_scheme.clone()))
            ),
        )
        .at(span_to_loc(arg_expr.span))
        .with_help(
            "pass a polymorphic function value (for example a let- or fn-bound generic function) that satisfies this `forall` contract",
        ),
    );
}

#[allow(clippy::too_many_arguments)]
fn enforce_param_contract_with_known_arg(
    arg_expr: &Expr,
    known_arg_ty: &Type,
    param_ty: &Type,
    arg_index: usize,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Type {
    match param_ty {
        Type::Existential { bounds, .. } => {
            enforce_existential_bounds_for_arg(bounds, known_arg_ty, arg_expr.span, unifier);
            known_arg_ty.clone()
        }
        Type::Forall(expected_scheme) => {
            if !argument_satisfies_rank2_param(
                arg_expr,
                known_arg_ty,
                expected_scheme,
                env,
                unifier,
                arg_index,
            ) {
                push_rank2_argument_mismatch_diag(unifier, arg_expr, arg_index, expected_scheme);
            }
            known_arg_ty.clone()
        }
        Type::Dynamic => infer_expr_bidir(arg_expr, env, unifier, records, traits, sum_types),
        _ => check_expr_bidir(
            arg_expr,
            param_ty,
            Reason::FunctionArg {
                param_index: arg_index,
            },
            env,
            unifier,
            records,
            traits,
            sum_types,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn infer_and_enforce_param_contract(
    arg_expr: &Expr,
    param_ty: &Type,
    arg_index: usize,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Type {
    match param_ty {
        Type::Existential { bounds, .. } => {
            let arg_ty = infer_expr_bidir(arg_expr, env, unifier, records, traits, sum_types);
            enforce_existential_bounds_for_arg(bounds, &arg_ty, arg_expr.span, unifier);
            arg_ty
        }
        Type::Forall(expected_scheme) => {
            let arg_ty = infer_expr_bidir(arg_expr, env, unifier, records, traits, sum_types);
            if !argument_satisfies_rank2_param(
                arg_expr,
                &arg_ty,
                expected_scheme,
                env,
                unifier,
                arg_index,
            ) {
                push_rank2_argument_mismatch_diag(unifier, arg_expr, arg_index, expected_scheme);
            }
            arg_ty
        }
        Type::Dynamic => infer_expr_bidir(arg_expr, env, unifier, records, traits, sum_types),
        _ => check_expr_bidir(
            arg_expr,
            param_ty,
            Reason::FunctionArg {
                param_index: arg_index,
            },
            env,
            unifier,
            records,
            traits,
            sum_types,
        ),
    }
}

#[derive(Debug, Clone)]
enum NarrowingGuardKind {
    OptionIsSome,
    OptionIsNone,
    ResultIsOk,
    ResultIsErr,
    SumVariantPredicate {
        sum_type_name: String,
        predicate_name: String,
    },
}

#[derive(Debug, Clone)]
struct NarrowingGuard {
    var_name: String,
    kind: NarrowingGuardKind,
}

#[derive(Debug, Clone, Default)]
struct ConditionNarrowings {
    true_bindings: BTreeMap<String, Type>,
    false_bindings: BTreeMap<String, Type>,
}

fn parse_narrowing_guard(func: &Expr, arg: &Expr) -> Option<NarrowingGuard> {
    let ExprKind::Var(var_name) = &arg.node else {
        return None;
    };

    let guard_kind = match &func.node {
        ExprKind::FieldAccess { expr, field } => match &expr.node {
            ExprKind::Var(module_name) if module_name == "Option" => match field.node.as_str() {
                "is_some" => Some(NarrowingGuardKind::OptionIsSome),
                "is_none" => Some(NarrowingGuardKind::OptionIsNone),
                _ => None,
            },
            ExprKind::Var(module_name) if module_name == "Result" => match field.node.as_str() {
                "is_ok" => Some(NarrowingGuardKind::ResultIsOk),
                "is_err" => Some(NarrowingGuardKind::ResultIsErr),
                _ => None,
            },
            ExprKind::Var(module_name) if field.node.starts_with("is_") => {
                Some(NarrowingGuardKind::SumVariantPredicate {
                    sum_type_name: module_name.clone(),
                    predicate_name: field.node.clone(),
                })
            }
            _ => None,
        },
        _ => None,
    }?;

    Some(NarrowingGuard {
        var_name: var_name.clone(),
        kind: guard_kind,
    })
}

fn match_narrowing_guard(expr: &Expr) -> Option<NarrowingGuard> {
    match &expr.node {
        ExprKind::Call { func, args } if args.len() == 1 => {
            parse_narrowing_guard(func, &args[0].value)
        }
        _ => None,
    }
}

fn merge_narrowing_maps(
    left: &mut BTreeMap<String, Type>,
    right: BTreeMap<String, Type>,
    unifier: &mut Unifier,
    span: Span,
) {
    for (name, incoming_ty) in right {
        if let Some(existing) = left.get(&name).cloned() {
            constrain_type_eq(
                unifier,
                &existing,
                &incoming_ty,
                &Provenance {
                    span,
                    reason: Reason::IfBranches,
                },
            );
            left.insert(name, unifier.substitution.apply(&existing));
        } else {
            left.insert(name, incoming_ty);
        }
    }
}

fn apply_condition_narrowings(
    env: &mut TypeEnv,
    narrowings: &BTreeMap<String, Type>,
    unifier: &Unifier,
) {
    for (name, ty) in narrowings {
        env.bind(
            name.clone(),
            TypeScheme::mono(unifier.substitution.apply(ty)),
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn narrowings_from_guard(
    guard: &NarrowingGuard,
    expr_span: Span,
    env: &TypeEnv,
    unifier: &mut Unifier,
    sum_types: &SumTypeRegistry,
) -> Option<ConditionNarrowings> {
    let scheme = env.lookup(&guard.var_name)?;

    let value_ty = instantiate_with_span(scheme, unifier, expr_span);
    let mut narrowings = ConditionNarrowings::default();
    let prov = Provenance {
        span: expr_span,
        reason: Reason::IfBranches,
    };

    match &guard.kind {
        NarrowingGuardKind::OptionIsSome => {
            let inner = unifier.fresh_type();
            constrain_type_eq(
                unifier,
                &value_ty,
                &Type::Option(Box::new(inner.clone())),
                &prov,
            );
            narrowings
                .true_bindings
                .insert(guard.var_name.clone(), inner);
        }
        NarrowingGuardKind::OptionIsNone => {
            let inner = unifier.fresh_type();
            constrain_type_eq(
                unifier,
                &value_ty,
                &Type::Option(Box::new(inner.clone())),
                &prov,
            );
            narrowings
                .false_bindings
                .insert(guard.var_name.clone(), inner);
        }
        NarrowingGuardKind::ResultIsOk => {
            let ok_ty = unifier.fresh_type();
            let err_ty = unifier.fresh_type();
            constrain_type_eq(
                unifier,
                &value_ty,
                &Type::Result(Box::new(ok_ty.clone()), Box::new(err_ty.clone())),
                &prov,
            );
            narrowings
                .true_bindings
                .insert(guard.var_name.clone(), ok_ty);
            narrowings
                .false_bindings
                .insert(guard.var_name.clone(), err_ty);
        }
        NarrowingGuardKind::ResultIsErr => {
            let ok_ty = unifier.fresh_type();
            let err_ty = unifier.fresh_type();
            constrain_type_eq(
                unifier,
                &value_ty,
                &Type::Result(Box::new(ok_ty.clone()), Box::new(err_ty.clone())),
                &prov,
            );
            narrowings
                .true_bindings
                .insert(guard.var_name.clone(), err_ty);
            narrowings
                .false_bindings
                .insert(guard.var_name.clone(), ok_ty);
        }
        NarrowingGuardKind::SumVariantPredicate {
            sum_type_name,
            predicate_name,
        } => {
            let mut resolved_value_ty = unifier.substitution.apply(&value_ty);
            if !matches!(&resolved_value_ty, Type::Sum(sum) if sum.name == *sum_type_name) {
                let expected_sum_ty = {
                    let mut maybe_unifier = Some(&mut *unifier);
                    sum_types.to_type_with(sum_type_name, &mut maybe_unifier)
                }?;
                constrain_type_eq(unifier, &value_ty, &expected_sum_ty, &prov);
                resolved_value_ty = unifier.substitution.apply(&value_ty);
            }

            let Type::Sum(sum_ty) = resolved_value_ty else {
                return None;
            };
            if sum_ty.name != *sum_type_name {
                return None;
            }

            let (matched_variant_name, matched_variant_fields) =
                sum_ty.variants.iter().find(|(variant_name, _)| {
                    variant_guard_predicate_name(variant_name) == *predicate_name
                })?;

            let remaining_variants: Vec<(String, Vec<Type>)> = sum_ty
                .variants
                .iter()
                .filter(|(variant_name, _)| variant_name != matched_variant_name)
                .cloned()
                .collect();

            if matched_variant_fields.len() == 1 {
                narrowings
                    .true_bindings
                    .insert(guard.var_name.clone(), matched_variant_fields[0].clone());
            }
            if remaining_variants.len() == 1 && remaining_variants[0].1.len() == 1 {
                narrowings
                    .false_bindings
                    .insert(guard.var_name.clone(), remaining_variants[0].1[0].clone());
            }
        }
    }

    Some(narrowings)
}

fn variant_guard_predicate_name(variant_name: &str) -> String {
    let mut out = String::from("is_");
    for (idx, ch) in variant_name.chars().enumerate() {
        if ch.is_uppercase() {
            if idx != 0 {
                out.push('_');
            }
            out.extend(ch.to_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn check_condition_and_collect_narrowings(
    condition: &Expr,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> ConditionNarrowings {
    if let Some(guard) = match_narrowing_guard(condition)
        && let Some(narrowings) =
            narrowings_from_guard(&guard, condition.span, env, unifier, sum_types)
    {
        return narrowings;
    }

    match &condition.node {
        ExprKind::UnaryOp { op, operand } if op.node == kea_ast::UnaryOp::Not => {
            let inner_narrowings = check_condition_and_collect_narrowings(
                operand, env, unifier, records, traits, sum_types,
            );
            ConditionNarrowings {
                true_bindings: inner_narrowings.false_bindings,
                false_bindings: inner_narrowings.true_bindings,
            }
        }
        ExprKind::BinaryOp { op, left, right } if op.node == BinOp::And => {
            let left_narrowings = check_condition_and_collect_narrowings(
                left, env, unifier, records, traits, sum_types,
            );

            env.push_scope();
            apply_condition_narrowings(env, &left_narrowings.true_bindings, unifier);
            let right_narrowings = check_condition_and_collect_narrowings(
                right, env, unifier, records, traits, sum_types,
            );
            env.pop_scope();

            let mut combined_true = left_narrowings.true_bindings;
            merge_narrowing_maps(
                &mut combined_true,
                right_narrowings.true_bindings,
                unifier,
                condition.span,
            );

            ConditionNarrowings {
                true_bindings: combined_true,
                false_bindings: BTreeMap::new(),
            }
        }
        ExprKind::BinaryOp { op, left, right } if op.node == BinOp::Or => {
            let left_narrowings = check_condition_and_collect_narrowings(
                left, env, unifier, records, traits, sum_types,
            );

            env.push_scope();
            apply_condition_narrowings(env, &left_narrowings.false_bindings, unifier);
            let right_narrowings = check_condition_and_collect_narrowings(
                right, env, unifier, records, traits, sum_types,
            );
            env.pop_scope();

            let mut combined_false = left_narrowings.false_bindings;
            merge_narrowing_maps(
                &mut combined_false,
                right_narrowings.false_bindings,
                unifier,
                condition.span,
            );

            ConditionNarrowings {
                true_bindings: BTreeMap::new(),
                false_bindings: combined_false,
            }
        }
        _ => {
            check_expr_bidir(
                condition,
                &Type::Bool,
                Reason::IfBranches,
                env,
                unifier,
                records,
                traits,
                sum_types,
            );
            ConditionNarrowings::default()
        }
    }
}

fn collect_resume_usage(
    expr: &Expr,
    inside_loop: bool,
    inside_lambda: bool,
    resume_count: &mut usize,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match &expr.node {
        ExprKind::Resume { value } => {
            *resume_count += 1;
            if inside_loop {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`resume` is not allowed inside loops in handler clauses",
                    )
                    .at(span_to_loc(expr.span)),
                );
            }
            if inside_lambda {
                diagnostics.push(
                    Diagnostic::error(
                        Category::TypeError,
                        "`resume` cannot be captured in a lambda",
                    )
                    .at(span_to_loc(expr.span)),
                );
            }
            collect_resume_usage(value, inside_loop, inside_lambda, resume_count, diagnostics);
        }
        ExprKind::Lit(_) | ExprKind::Var(_) | ExprKind::None | ExprKind::Atom(_) | ExprKind::Wildcard => {}
        ExprKind::Let { value, .. } => {
            collect_resume_usage(value, inside_loop, inside_lambda, resume_count, diagnostics);
        }
        ExprKind::Lambda { body, .. } => {
            collect_resume_usage(body, inside_loop, true, resume_count, diagnostics);
        }
        ExprKind::Call { func, args } => {
            collect_resume_usage(func, inside_loop, inside_lambda, resume_count, diagnostics);
            for arg in args {
                collect_resume_usage(
                    &arg.value,
                    inside_loop,
                    inside_lambda,
                    resume_count,
                    diagnostics,
                );
            }
        }
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_resume_usage(
                condition,
                inside_loop,
                inside_lambda,
                resume_count,
                diagnostics,
            );
            collect_resume_usage(
                then_branch,
                inside_loop,
                inside_lambda,
                resume_count,
                diagnostics,
            );
            if let Some(otherwise) = else_branch {
                collect_resume_usage(
                    otherwise,
                    inside_loop,
                    inside_lambda,
                    resume_count,
                    diagnostics,
                );
            }
        }
        ExprKind::Case { scrutinee, arms } => {
            collect_resume_usage(
                scrutinee,
                inside_loop,
                inside_lambda,
                resume_count,
                diagnostics,
            );
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_resume_usage(
                        guard,
                        inside_loop,
                        inside_lambda,
                        resume_count,
                        diagnostics,
                    );
                }
                collect_resume_usage(
                    &arm.body,
                    inside_loop,
                    inside_lambda,
                    resume_count,
                    diagnostics,
                );
            }
        }
        ExprKind::Cond { arms } => {
            for arm in arms {
                collect_resume_usage(
                    &arm.condition,
                    inside_loop,
                    inside_lambda,
                    resume_count,
                    diagnostics,
                );
                collect_resume_usage(
                    &arm.body,
                    inside_loop,
                    inside_lambda,
                    resume_count,
                    diagnostics,
                );
            }
        }
        ExprKind::For(for_expr) => {
            for clause in &for_expr.clauses {
                match clause {
                    ForClause::Generator { source, .. } => collect_resume_usage(
                        source,
                        true,
                        inside_lambda,
                        resume_count,
                        diagnostics,
                    ),
                    ForClause::Guard(guard) => collect_resume_usage(
                        guard,
                        true,
                        inside_lambda,
                        resume_count,
                        diagnostics,
                    ),
                }
            }
            collect_resume_usage(
                &for_expr.body,
                true,
                inside_lambda,
                resume_count,
                diagnostics,
            );
        }
        ExprKind::Use(use_expr) => {
            collect_resume_usage(
                &use_expr.rhs,
                inside_loop,
                inside_lambda,
                resume_count,
                diagnostics,
            );
        }
        ExprKind::BinaryOp { left, right, .. } => {
            collect_resume_usage(left, inside_loop, inside_lambda, resume_count, diagnostics);
            collect_resume_usage(right, inside_loop, inside_lambda, resume_count, diagnostics);
        }
        ExprKind::UnaryOp { operand, .. } | ExprKind::As { expr: operand, .. } => {
            collect_resume_usage(
                operand,
                inside_loop,
                inside_lambda,
                resume_count,
                diagnostics,
            );
        }
        ExprKind::WhenGuard { body, condition } => {
            collect_resume_usage(body, inside_loop, inside_lambda, resume_count, diagnostics);
            collect_resume_usage(
                condition,
                inside_loop,
                inside_lambda,
                resume_count,
                diagnostics,
            );
        }
        ExprKind::Range { start, end, .. } => {
            collect_resume_usage(start, inside_loop, inside_lambda, resume_count, diagnostics);
            collect_resume_usage(end, inside_loop, inside_lambda, resume_count, diagnostics);
        }
        ExprKind::Tuple(items) | ExprKind::List(items) | ExprKind::Block(items) => {
            for item in items {
                collect_resume_usage(item, inside_loop, inside_lambda, resume_count, diagnostics);
            }
        }
        ExprKind::Record { fields, spread, .. } | ExprKind::AnonRecord { fields, spread } => {
            for (_, value) in fields {
                collect_resume_usage(value, inside_loop, inside_lambda, resume_count, diagnostics);
            }
            if let Some(spread_expr) = spread {
                collect_resume_usage(
                    spread_expr,
                    inside_loop,
                    inside_lambda,
                    resume_count,
                    diagnostics,
                );
            }
        }
        ExprKind::FieldAccess { expr, .. } => {
            collect_resume_usage(expr, inside_loop, inside_lambda, resume_count, diagnostics);
        }
        ExprKind::Constructor { args, .. } => {
            for arg in args {
                collect_resume_usage(
                    &arg.value,
                    inside_loop,
                    inside_lambda,
                    resume_count,
                    diagnostics,
                );
            }
        }
        ExprKind::StringInterp(parts) => {
            for part in parts {
                if let kea_ast::StringInterpPart::Expr(inner) = part {
                    collect_resume_usage(
                        inner,
                        inside_loop,
                        inside_lambda,
                        resume_count,
                        diagnostics,
                    );
                }
            }
        }
        ExprKind::MapLiteral(entries) => {
            for (k, v) in entries {
                collect_resume_usage(k, inside_loop, inside_lambda, resume_count, diagnostics);
                collect_resume_usage(v, inside_loop, inside_lambda, resume_count, diagnostics);
            }
        }
        ExprKind::Handle {
            expr: handled,
            clauses: _,
            then_clause,
        } => {
            // Nested handler clauses have their own resume context.
            collect_resume_usage(
                handled,
                inside_loop,
                inside_lambda,
                resume_count,
                diagnostics,
            );
            if let Some(then_expr) = then_clause {
                collect_resume_usage(
                    then_expr,
                    inside_loop,
                    inside_lambda,
                    resume_count,
                    diagnostics,
                );
            }
        }
        ExprKind::Spawn { value, config } => {
            collect_resume_usage(value, inside_loop, inside_lambda, resume_count, diagnostics);
            if let Some(cfg) = config {
                for entry in [
                    cfg.mailbox_size.as_ref(),
                    cfg.supervision.as_ref(),
                    cfg.max_restarts.as_ref(),
                    cfg.call_timeout.as_ref(),
                ]
                .into_iter()
                .flatten()
                {
                    collect_resume_usage(
                        entry,
                        inside_loop,
                        inside_lambda,
                        resume_count,
                        diagnostics,
                    );
                }
            }
        }
        ExprKind::Await { expr, .. } => {
            collect_resume_usage(expr, inside_loop, inside_lambda, resume_count, diagnostics);
        }
        ExprKind::StreamBlock { body, .. } => {
            collect_resume_usage(body, inside_loop, inside_lambda, resume_count, diagnostics);
        }
        ExprKind::Yield { value } => {
            collect_resume_usage(value, inside_loop, inside_lambda, resume_count, diagnostics);
        }
        ExprKind::YieldFrom { source } => {
            collect_resume_usage(source, inside_loop, inside_lambda, resume_count, diagnostics);
        }
        ExprKind::ActorSend { actor, args, .. } | ExprKind::ActorCall { actor, args, .. } => {
            collect_resume_usage(actor, inside_loop, inside_lambda, resume_count, diagnostics);
            for arg in args {
                collect_resume_usage(arg, inside_loop, inside_lambda, resume_count, diagnostics);
            }
        }
        ExprKind::ControlSend { actor, signal } => {
            collect_resume_usage(actor, inside_loop, inside_lambda, resume_count, diagnostics);
            collect_resume_usage(signal, inside_loop, inside_lambda, resume_count, diagnostics);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn infer_handle_expr_type(
    expr_span: Span,
    handled: &Expr,
    clauses: &[kea_ast::HandleClause],
    then_clause: Option<&Expr>,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Type {
    let handled_ty = infer_expr_bidir(handled, env, unifier, records, traits, sum_types);
    let mut result_ty = handled_ty.clone();

    if let Some(then_expr) = then_clause {
        let then_ty = infer_expr_bidir(then_expr, env, unifier, records, traits, sum_types);
        let out_ty = unifier.fresh_type();
        let expected = Type::Function(FunctionType {
            params: vec![handled_ty.clone()],
            ret: Box::new(out_ty.clone()),
            effects: EffectRow::pure(),
        });
        constrain_type_eq(
            unifier,
            &then_ty,
            &expected,
            &Provenance {
                span: then_expr.span,
                reason: Reason::TypeAscription,
            },
        );
        result_ty = out_ty;
    }

    let Some(first_clause) = clauses.first() else {
        unifier.push_error(
            Diagnostic::error(
                Category::TypeError,
                "handle expression requires at least one operation clause",
            )
            .at(span_to_loc(expr_span)),
        );
        return unifier.fresh_type();
    };

    let target_effect = first_clause.effect.node.clone();
    let module_path = env
        .module_aliases
        .get(&target_effect)
        .cloned()
        .unwrap_or_else(|| format!("Kea.{target_effect}"));
    let mut seen_ops = BTreeSet::new();

    for clause in clauses {
        if clause.effect.node != target_effect {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "all clauses in a handle expression must target `{target_effect}`; found `{}`",
                        clause.effect.node
                    ),
                )
                .at(span_to_loc(clause.effect.span)),
            );
            continue;
        }
        if !seen_ops.insert(clause.operation.node.clone()) {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "duplicate handler clause for `{target_effect}.{}(...)`",
                        clause.operation.node
                    ),
                )
                .at(span_to_loc(clause.operation.span)),
            );
        }

        let Some(op_scheme) = env.lookup_module_type_scheme(&module_path, &clause.operation.node)
        else {
            unifier.push_error(
                Diagnostic::error(
                    Category::UndefinedName,
                    format!(
                        "effect `{target_effect}` has no operation `{}`",
                        clause.operation.node
                    ),
                )
                .at(span_to_loc(clause.operation.span)),
            );
            continue;
        };
        let op_ty = instantiate_with_span(&op_scheme, unifier, clause.span);
        let resolved_op_ty = unifier.substitution.apply(&op_ty);
        let Type::Function(op_fn) = resolved_op_ty else {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "effect operation `{target_effect}.{}(...)` is not callable",
                        clause.operation.node
                    ),
                )
                .at(span_to_loc(clause.operation.span)),
            );
            continue;
        };

        if clause.args.len() != op_fn.params.len() {
            unifier.push_error(
                Diagnostic::error(
                    Category::ArityMismatch,
                    format!(
                        "handler clause `{target_effect}.{}(...)` expects {} argument(s), got {}",
                        clause.operation.node,
                        op_fn.params.len(),
                        clause.args.len(),
                    ),
                )
                .at(span_to_loc(clause.span)),
            );
        }

        let mut clause_env = env.clone();
        clause_env.push_scope();
        for (pattern, param_ty) in clause.args.iter().zip(op_fn.params.iter()) {
            infer_pattern(pattern, param_ty, &mut clause_env, unifier, records, sum_types);
        }

        let mut resume_count = 0usize;
        let mut usage_diags = Vec::new();
        collect_resume_usage(
            &clause.body,
            false,
            false,
            &mut resume_count,
            &mut usage_diags,
        );
        if resume_count > 1 {
            usage_diags.push(
                Diagnostic::error(
                    Category::TypeError,
                    "handler clause may resume at most once",
                )
                .at(span_to_loc(clause.span)),
            );
        }
        for diag in usage_diags {
            unifier.push_error(diag);
        }

        clause_env.push_resume_context((*op_fn.ret).clone(), result_ty.clone());
        let clause_ty = infer_expr_bidir(
            &clause.body,
            &mut clause_env,
            unifier,
            records,
            traits,
            sum_types,
        );
        constrain_type_eq(
            unifier,
            &clause_ty,
            &result_ty,
            &Provenance {
                span: clause.body.span,
                reason: Reason::TypeAscription,
            },
        );
        clause_env.pop_scope();
    }

    if let Some(all_ops) = env.module_function_names(&module_path) {
        let missing = all_ops
            .into_iter()
            .filter(|op| !seen_ops.contains(op))
            .collect::<Vec<_>>();
        if !missing.is_empty() {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    format!(
                        "handler for `{target_effect}` is missing clause(s): {}",
                        missing.join(", ")
                    ),
                )
                .at(span_to_loc(expr_span)),
            );
        }
    }

    result_ty
}

/// Infer the type of an expression.
///
/// Uses eager unification: types are unified as the AST is walked, so
/// downstream inference sees resolved types immediately. This is essential
/// for let-generalization (need to know what's resolved before generalizing).
fn infer_expr_bidir(
    expr: &Expr,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Type {
    let prov = |reason: Reason| -> Provenance {
        Provenance {
            span: expr.span,
            reason,
        }
    };

    match &expr.node {
        // -- Literals --
        ExprKind::Lit(lit) => match lit {
            Lit::Int(_) => Type::Int,
            Lit::Float(_) => Type::Float,
            Lit::Bool(_) => Type::Bool,
            Lit::String(_) => Type::String,
            Lit::Unit => Type::Unit,
        },

        // -- None --
        ExprKind::None => {
            let inner = unifier.fresh_type();
            Type::Option(Box::new(inner))
        }

        // -- Atom literal --
        ExprKind::Atom(_) => Type::Atom,

        // -- Variable reference --
        ExprKind::Var(name) => match env.lookup(name) {
            Some(scheme) => instantiate_with_span(scheme, unifier, expr.span),
            None => {
                unifier.push_error(
                    Diagnostic::error(
                        Category::UndefinedName,
                        format!("undefined variable `{name}`"),
                    )
                    .at(span_to_loc(expr.span)),
                );
                unifier.fresh_type()
            }
        },

        // -- Let binding (with letrec for lambdas) --
        ExprKind::Let {
            pattern,
            annotation,
            value,
        } => {
            // For recursive functions: pre-bind the name with a fresh type var
            // in a temporary scope so the body can refer to itself.
            let is_recursive = matches!(value.node, ExprKind::Lambda { .. });
            let let_name = match &pattern.node {
                PatternKind::Var(n) => Some(n.clone()),
                _ => None,
            };
            let rec_ty = if is_recursive {
                let tv = unifier.fresh_type();
                env.push_scope();
                if let Some(ref n) = let_name {
                    env.bind(n.clone(), TypeScheme::mono(tv.clone()));
                }
                Some(tv)
            } else {
                None
            };

            // When there's a type annotation, resolve it first and use
            // check_expr_bidir so the expected type is available for
            // bidirectional disambiguation (e.g. scoped constructors).
            let resolved_annotation = annotation.as_ref().and_then(|ann| {
                resolve_annotation_or_bare_df(&ann.node, records, Some(sum_types), unifier)
                    .map(|ty| (ty, ann))
            });

            let binding_ty = if let Some((ref declared_ty, _ann)) = resolved_annotation {
                check_expr_bidir(
                    value,
                    declared_ty,
                    Reason::LetAnnotation,
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                )
            } else {
                infer_expr_bidir(value, env, unifier, records, traits, sum_types)
            };

            // Pop the pre-binding scope before generalizing, so the mono
            // self-reference doesn't poison generalization.
            if let Some(rec_ty) = &rec_ty {
                env.pop_scope();
                constrain_type_eq(unifier, rec_ty, &binding_ty, &prov(Reason::LetAnnotation));
            }

            if let Some(ann) = annotation
                && resolved_annotation.is_none()
            {
                push_annotation_resolution_error(
                    unifier,
                    &ann.node,
                    ann.span,
                    records,
                    Some(sum_types),
                );
            }
            // Bind the pattern variables.
            match &pattern.node {
                PatternKind::Var(n) => {
                    let scheme = generalize(
                        &binding_ty,
                        env,
                        &unifier.substitution,
                        &unifier.lacks,
                        &unifier.trait_bounds,
                        &unifier.type_var_kinds,
                    );
                    env.bind(n.clone(), scheme);
                }
                _ => {
                    // Destructuring let: infer_pattern binds all names.
                    // Check irrefutability first.
                    if !crate::exhaustive::is_irrefutable(pattern, &binding_ty, sum_types) {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::NonExhaustive,
                                "refutable pattern in let binding; use `case` for sum type destructuring"
                                    .to_string(),
                            )
                            .at(span_to_loc(pattern.span)),
                        );
                    }
                    infer_pattern(pattern, &binding_ty, env, unifier, records, sum_types);
                }
            }
            Type::Unit
        }

        // -- Lambda --
        ExprKind::Lambda {
            params,
            body,
            return_annotation,
        } => {
            unifier.enter_lambda();
            env.push_scope();
            let mut param_types = Vec::new();
            for param in params {
                let param_ty = unifier.fresh_type();
                if let Some(ann) = &param.annotation {
                    if let Some(declared_ty) =
                        resolve_annotation_or_bare_df(&ann.node, records, Some(sum_types), unifier)
                    {
                        constrain_type_eq(
                            unifier,
                            &param_ty,
                            &declared_ty,
                            &prov(Reason::LetAnnotation),
                        );
                    } else if let Some((name, expected, got)) =
                        annotation_type_arity_mismatch(&ann.node, records, Some(sum_types))
                    {
                        push_annotation_arity_mismatch(unifier, ann.span, &name, expected, got);
                    }
                }
                match &param.pattern.node {
                    PatternKind::Var(name) => {
                        env.bind(name.clone(), TypeScheme::mono(param_ty.clone()));
                    }
                    _ => {
                        // Destructuring parameter: check irrefutability, then bind.
                        if !pattern_is_irrefutable(&param.pattern) {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::NonExhaustive,
                                    "refutable pattern in function parameter; \
                                     use `case` inside the body for refutable patterns"
                                        .to_string(),
                                )
                                .at(span_to_loc(param.pattern.span)),
                            );
                        }
                        infer_pattern(&param.pattern, &param_ty, env, unifier, records, sum_types);
                    }
                }
                param_types.push(param_ty);
            }
            let mut body_ty = infer_expr_bidir(body, env, unifier, records, traits, sum_types);
            if let Some(ann) = return_annotation {
                if let Some(declared_ret) =
                    resolve_annotation_or_bare_df(&ann.node, records, Some(sum_types), unifier)
                {
                    body_ty = check_expr_bidir(
                        body,
                        &declared_ret,
                        Reason::LetAnnotation,
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                } else if let Some((name, expected, got)) =
                    annotation_type_arity_mismatch(&ann.node, records, Some(sum_types))
                {
                    push_annotation_arity_mismatch(unifier, ann.span, &name, expected, got);
                }
            }
            env.pop_scope();
            unifier.exit_lambda();

            Type::Function(FunctionType {
                params: param_types,
                ret: Box::new(body_ty),
                effects: EffectRow::pure(),
            })
        }

        // -- Function application --
        ExprKind::Call { func, args } => {
            let (call_signature, bound_args) =
                resolve_bound_call_args(func, args, expr.span, env, unifier);

            let func_ty = infer_expr_bidir(func, env, unifier, records, traits, sum_types);
            let mut arg_types = infer_bound_args_with_param_contracts(
                &bound_args,
                call_signature.as_ref(),
                None,
                env,
                unifier,
                records,
                traits,
                sum_types,
            );

            let callable_ty = instantiate_callable_type_for_call(&func_ty, unifier, expr.span);
            let resolved_callable = unifier.substitution.apply(&callable_ty);
            let ret_ty = unifier.fresh_type();

            if let Type::Function(ft) = &resolved_callable
                && ft.params.len() == bound_args.len()
            {
                let mut default_env = env.clone();
                default_env.push_scope();
                for (i, bound_arg) in bound_args.iter().enumerate() {
                    if let Some(param_ty) = ft.params.get(i) {
                        let known_arg_ty = arg_types[i].clone();
                        arg_types[i] = match bound_arg {
                            BoundArg::Provided(arg_expr) => enforce_param_contract_with_known_arg(
                                arg_expr,
                                &known_arg_ty,
                                param_ty,
                                i,
                                env,
                                unifier,
                                records,
                                traits,
                                sum_types,
                            ),
                            BoundArg::Default(arg_expr) => enforce_param_contract_with_known_arg(
                                arg_expr,
                                &known_arg_ty,
                                param_ty,
                                i,
                                &mut default_env,
                                unifier,
                                records,
                                traits,
                                sum_types,
                            ),
                        };
                        if let Some(param_name) = call_signature
                            .as_ref()
                            .and_then(|sig| sig.params.get(i))
                            .and_then(|param| param.name.as_ref())
                        {
                            default_env
                                .bind(param_name.clone(), TypeScheme::mono(arg_types[i].clone()));
                        }
                    }
                }
                constrain_type_eq(
                    unifier,
                    &ret_ty,
                    &ft.ret,
                    &prov(Reason::FunctionArg { param_index: 0 }),
                );
                unifier.note_evidence_site(expr.span, &resolved_callable);
            } else {
                let expected_params = params_for_call_unification(&resolved_callable, &arg_types);
                let expected_func_ty = Type::Function(FunctionType {
                    params: expected_params,
                    ret: Box::new(ret_ty.clone()),
                    effects: EffectRow::pure(),
                });

                constrain_type_eq(
                    unifier,
                    &expected_func_ty,
                    &resolved_callable,
                    &prov(Reason::FunctionArg { param_index: 0 }),
                );
                unifier.note_evidence_site(expr.span, &resolved_callable);
            }

            note_existential_pack_sites(unifier, expr.span, &callable_ty, &arg_types);

            ret_ty
        }

        // -- If expression --
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let narrowings = check_condition_and_collect_narrowings(
                condition, env, unifier, records, traits, sum_types,
            );

            env.push_scope();
            apply_condition_narrowings(env, &narrowings.true_bindings, unifier);
            let then_ty = infer_expr_bidir(then_branch, env, unifier, records, traits, sum_types);
            env.pop_scope();

            match else_branch {
                Some(else_expr) => {
                    env.push_scope();
                    apply_condition_narrowings(env, &narrowings.false_bindings, unifier);
                    check_expr_bidir(
                        else_expr,
                        &then_ty,
                        Reason::IfBranches,
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                    env.pop_scope();
                    then_ty
                }
                None => {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::TypeError,
                            "internal error: `if` without `else` reached type checker",
                        )
                        .at(span_to_loc(expr.span)),
                    );
                    unifier.fresh_type()
                }
            }
        }

        ExprKind::Range { start, end, .. } => {
            let start_ty = infer_expr_bidir(start, env, unifier, records, traits, sum_types);
            let end_ty = infer_expr_bidir(end, env, unifier, records, traits, sum_types);
            constrain_type_eq(unifier, &start_ty, &end_ty, &prov(Reason::RangeBounds));
            let elem_ty = unifier.substitution.apply(&start_ty);
            constrain_trait_obligation(unifier, &elem_ty, "Orderable", &prov(Reason::RangeBounds));
            Type::Opaque {
                name: "Range".to_string(),
                params: vec![elem_ty],
            }
        }

        // -- Binary operators --
        ExprKind::BinaryOp { op, left, right } => {
            let left_ty = infer_expr_bidir(left, env, unifier, records, traits, sum_types);
            let right_ty = infer_expr_bidir(right, env, unifier, records, traits, sum_types);
            let op_name = binop_name(op.node);

            match op.node {
                // Arithmetic: both sides same type, result same type.
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    let left_resolved = unifier.substitution.apply(&left_ty);
                    let right_resolved = unifier.substitution.apply(&right_ty);
                    if let Some(decimal_ty) = infer_decimal_binary_result_fallback(
                        op.node,
                        &left_resolved,
                        &right_resolved,
                        unifier,
                    ) {
                        decimal_ty
                    } else {
                        constrain_type_eq(
                            unifier,
                            &left_ty,
                            &right_ty,
                            &prov(Reason::BinaryOp(op_name)),
                        );
                        left_ty
                    }
                }
                // Comparison: both sides same type, result Bool.
                BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => {
                    constrain_type_eq(
                        unifier,
                        &left_ty,
                        &right_ty,
                        &prov(Reason::BinaryOp(op_name)),
                    );
                    Type::Bool
                }
                // Logical: both sides Bool, result Bool.
                BinOp::And | BinOp::Or => {
                    constrain_type_eq(
                        unifier,
                        &Type::Bool,
                        &left_ty,
                        &prov(Reason::BinaryOp(op_name)),
                    );
                    constrain_type_eq(
                        unifier,
                        &Type::Bool,
                        &right_ty,
                        &prov(Reason::BinaryOp(op_name)),
                    );
                    Type::Bool
                }
                // Membership: x in collection / x not in collection → Bool.
                // RHS must be List(T), Set(T), Map(K,V), or String.
                // LHS must match the element type.
                BinOp::In | BinOp::NotIn => {
                    let resolved_right = unifier.substitution.apply(&right_ty);
                    match &resolved_right {
                        Type::List(elem) => {
                            constrain_type_eq(
                                unifier,
                                &left_ty,
                                elem,
                                &prov(Reason::BinaryOp(op_name)),
                            );
                        }
                        Type::Set(elem) => {
                            constrain_type_eq(
                                unifier,
                                &left_ty,
                                elem,
                                &prov(Reason::BinaryOp(op_name)),
                            );
                        }
                        Type::Map(key, _) => {
                            constrain_type_eq(
                                unifier,
                                &left_ty,
                                key,
                                &prov(Reason::BinaryOp(op_name)),
                            );
                        }
                        Type::String => {
                            constrain_type_eq(
                                unifier,
                                &left_ty,
                                &Type::String,
                                &prov(Reason::BinaryOp(op_name)),
                            );
                        }
                        Type::Opaque { name, params } if name == "Range" && params.len() == 1 => {
                            constrain_type_eq(
                                unifier,
                                &left_ty,
                                &params[0],
                                &prov(Reason::BinaryOp(op_name)),
                            );
                        }
                        _ => {
                            // Allow unresolved types — default to List(T)
                            let elem_ty = unifier.fresh_type();
                            let list_ty = Type::List(Box::new(elem_ty.clone()));
                            constrain_type_eq(
                                unifier,
                                &right_ty,
                                &list_ty,
                                &prov(Reason::BinaryOp(op_name)),
                            );
                            constrain_type_eq(
                                unifier,
                                &left_ty,
                                &elem_ty,
                                &prov(Reason::BinaryOp(op_name)),
                            );
                        }
                    }
                    Type::Bool
                }
                // ++ (Concatenable) and <> (Monoid): both sides same type, result same type
                BinOp::Concat | BinOp::Combine => {
                    constrain_type_eq(
                        unifier,
                        &left_ty,
                        &right_ty,
                        &prov(Reason::BinaryOp(op_name)),
                    );
                    left_ty
                }
            }
        }

        // -- Tuple --
        ExprKind::Tuple(elems) => {
            let elem_types: Vec<Type> = elems
                .iter()
                .map(|e| infer_expr_bidir(e, env, unifier, records, traits, sum_types))
                .collect();
            Type::Tuple(elem_types)
        }

        // -- List --
        ExprKind::List(elems) => {
            if elems.is_empty() {
                let elem_ty = unifier.fresh_type();
                Type::List(Box::new(elem_ty))
            } else {
                let first_ty =
                    infer_expr_bidir(&elems[0], env, unifier, records, traits, sum_types);
                for elem in &elems[1..] {
                    let elem_ty = infer_expr_bidir(elem, env, unifier, records, traits, sum_types);
                    constrain_type_eq(unifier, &first_ty, &elem_ty, &prov(Reason::LetAnnotation));
                }
                Type::List(Box::new(first_ty))
            }
        }

        // -- Anonymous record --
        ExprKind::AnonRecord { fields, spread } => {
            let mut seen_labels = BTreeSet::new();
            let mut field_types = Vec::with_capacity(fields.len());
            for (name, expr) in fields {
                if !seen_labels.insert(name.node.clone()) {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::TypeMismatch,
                            format!("duplicate field `{}` in anonymous record", name.node),
                        )
                        .at(span_to_loc(name.span)),
                    );
                }
                let ty = infer_expr_bidir(expr, env, unifier, records, traits, sum_types);
                field_types.push((Label::new(name.node.clone()), ty));
            }
            if let Some(spread_expr) = spread {
                let spread_ty =
                    infer_expr_bidir(spread_expr, env, unifier, records, traits, sum_types);
                // The spread provides a base record. The result extends it with explicit fields.
                // Create an open row for the spread and unify.
                let tail = unifier.fresh_row_var();
                for (label, _) in &field_types {
                    constrain_lacks(
                        unifier,
                        tail,
                        label.clone(),
                        &prov(Reason::RowExtension {
                            label: label.clone(),
                        }),
                    );
                }
                let spread_row = RowType::open(vec![], tail);
                constrain_type_eq(
                    unifier,
                    &spread_ty,
                    &Type::AnonRecord(spread_row),
                    &prov(Reason::RecordField {
                        label: Label::new("..spread".to_string()),
                    }),
                );
                // Result: explicit fields + whatever the spread had (open tail)
                Type::AnonRecord(RowType::open(field_types, tail))
            } else {
                Type::AnonRecord(RowType::closed(field_types))
            }
        }

        // -- Field access --
        ExprKind::FieldAccess { expr: obj, field } => {
            if let ExprKind::Var(module_name) = &obj.node
                && env.lookup(module_name).is_none()
                && looks_like_module_name(module_name)
            {
                if let Some(scheme) = env.resolve_qualified(module_name, &field.node) {
                    return instantiate_with_span(scheme, unifier, field.span);
                }
                if env.has_qualified_module(module_name) {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::UndefinedName,
                            format!("module {module_name} has no function `{}`", field.node),
                        )
                        .at(span_to_loc(field.span)),
                    );
                    return unifier.fresh_type();
                }

                if let Some(trait_info) = traits.lookup_trait(module_name) {
                    if let Some(method) = trait_info.methods.iter().find(|m| m.name == field.node) {
                        return instantiate_trait_method_type(
                            trait_info,
                            module_name,
                            method,
                            unifier,
                        );
                    }
                    unifier.push_error(
                        Diagnostic::error(
                            Category::UndefinedName,
                            format!("trait `{module_name}` has no method `{}`", field.node),
                        )
                        .at(span_to_loc(field.span)),
                    );
                    return unifier.fresh_type();
                }

                // Check if the name is a sum type — qualified constructor: SumType.Variant
                if sum_types.lookup(module_name).is_some() {
                    if sum_types.lookup_variant_in_type(&field.node, module_name).is_some()
                    {
                        // This is a qualified constructor reference like `ApiResponse.Error`.
                        // Don't return a value yet — it might be called with args (handled
                        // as Call(FieldAccess(...), args) in the Call branch) or used bare
                        // as a unit constructor. Record the resolved type name in annotations
                        // so the evaluator knows which type to construct.
                        if let Some(inst) = sum_types.instantiate_variant_for_type(
                            &field.node,
                            Some(module_name),
                            unifier,
                        ) {
                            // Record in type annotations for evaluator dispatch.
                            unifier.record_resolved_variant(field.span, module_name.to_string());
                            // If the variant has no fields, it's a bare constructor (unit variant).
                            if inst.field_types.is_empty() {
                                return inst.sum_type;
                            }
                            // If it has fields, return a function type so it can be called.
                            let param_types: Vec<Type> =
                                inst.field_types.iter().map(|f| f.ty.clone()).collect();
                            return Type::Function(FunctionType {
                                params: param_types,
                                ret: Box::new(inst.sum_type),
                                effects: EffectRow::pure(),
                            });
                        }
                    }
                    unifier.push_error(
                        Diagnostic::error(
                            Category::UndefinedName,
                            format!(
                                "type `{module_name}` has no variant `{}`",
                                field.node
                            ),
                        )
                        .at(span_to_loc(field.span)),
                    );
                    return unifier.fresh_type();
                }

                unifier.push_error(
                    Diagnostic::error(
                        Category::UndefinedName,
                        format!("unknown module `{module_name}`"),
                    )
                    .at(span_to_loc(obj.span)),
                );
                return unifier.fresh_type();
            }

            let obj_ty = infer_expr_bidir(obj, env, unifier, records, traits, sum_types);
            let resolved_obj_ty = unifier.substitution.apply(&obj_ty);

            if field.node == "value"
                && let Type::Opaque { name, params } = &resolved_obj_ty
                && let Some(underlying) =
                    instantiate_opaque_target(name, params, records, Some(sum_types))
            {
                return underlying;
            }

            let field_ty = unifier.fresh_type();
            let rest = unifier.fresh_row_var();

            // The object must have a row containing this field.
            let expected_row = RowType::open(
                vec![(Label::new(field.node.clone()), field_ty.clone())],
                rest,
            );
            let expected_ty = Type::AnonRecord(expected_row);

            constrain_type_eq(
                unifier,
                &expected_ty,
                &obj_ty,
                &prov(Reason::RecordField {
                    label: Label::new(field.node.clone()),
                }),
            );

            field_ty
        }

        // -- Block --
        ExprKind::Block(exprs) => {
            if exprs.is_empty() {
                return Type::Unit;
            }
            env.push_scope();
            let mut last_ty = Type::Unit;
            let mut idx = 0usize;
            while idx < exprs.len() {
                let current = &exprs[idx];
                if let ExprKind::Use(_) = &current.node {
                    last_ty =
                        infer_use_chain_expr(exprs, idx, env, unifier, records, traits, sum_types);
                    // `use` consumes the rest of the block.
                    break;
                }
                last_ty = infer_expr_bidir(current, env, unifier, records, traits, sum_types);
                idx += 1;
            }
            env.pop_scope();
            last_ty
        }

        ExprKind::WhenGuard { body, condition } => {
            check_expr_bidir(
                condition,
                &Type::Bool,
                Reason::IfBranches,
                env,
                unifier,
                records,
                traits,
                sum_types,
            );
            let body_ty = infer_expr_bidir(body, env, unifier, records, traits, sum_types);
            constrain_type_eq(unifier, &body_ty, &Type::Unit, &prov(Reason::IfBranches));
            Type::Unit
        }

        // -- Constructor (Some, Ok, Err) --
        ExprKind::Constructor { name, args } => {
            match name.node.as_str() {
                "Some" => {
                    if args.len() != 1 {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                format!("`Some` expects 1 argument, got {}", args.len()),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                        return unifier.fresh_type();
                    }
                    if let Some(label) = &args[0].label {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                "`Some` does not accept labeled arguments",
                            )
                            .at(span_to_loc(label.span)),
                        );
                    }
                    let inner =
                        infer_expr_bidir(&args[0].value, env, unifier, records, traits, sum_types);
                    Type::Option(Box::new(inner))
                }
                "Ok" => {
                    if args.len() != 1 {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                format!("`Ok` expects 1 argument, got {}", args.len()),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                        return unifier.fresh_type();
                    }
                    if let Some(label) = &args[0].label {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                "`Ok` does not accept labeled arguments",
                            )
                            .at(span_to_loc(label.span)),
                        );
                    }
                    let ok_ty =
                        infer_expr_bidir(&args[0].value, env, unifier, records, traits, sum_types);
                    let err_ty = unifier.fresh_type();
                    Type::Result(Box::new(ok_ty), Box::new(err_ty))
                }
                "Err" => {
                    if args.len() != 1 {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                format!("`Err` expects 1 argument, got {}", args.len()),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                        return unifier.fresh_type();
                    }
                    if let Some(label) = &args[0].label {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                "`Err` does not accept labeled arguments",
                            )
                            .at(span_to_loc(label.span)),
                        );
                    }
                    let err_ty =
                        infer_expr_bidir(&args[0].value, env, unifier, records, traits, sum_types);
                    let ok_ty = unifier.fresh_type();
                    Type::Result(Box::new(ok_ty), Box::new(err_ty))
                }
                "None" => Type::Option(Box::new(unifier.fresh_type())),
                _ => {
                    if let Some(info) = records.lookup_opaque(&name.node) {
                        if args.len() != 1 {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::ArityMismatch,
                                    format!(
                                        "`{}` expects 1 argument, got {}",
                                        name.node,
                                        args.len()
                                    ),
                                )
                                .at(span_to_loc(expr.span)),
                            );
                            return unifier.fresh_type();
                        }

                        let params: Vec<Type> =
                            info.params.iter().map(|_| unifier.fresh_type()).collect();
                        let opaque_ty = Type::Opaque {
                            name: name.node.clone(),
                            params: params.clone(),
                        };
                        let Some(underlying_ty) = instantiate_opaque_target(
                            &name.node,
                            &params,
                            records,
                            Some(sum_types),
                        ) else {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::TypeMismatch,
                                    format!(
                                        "cannot resolve underlying type for opaque `{}`",
                                        name.node
                                    ),
                                )
                                .at(span_to_loc(name.span)),
                            );
                            return unifier.fresh_type();
                        };

                        let arg_ty = infer_expr_bidir(
                            &args[0].value,
                            env,
                            unifier,
                            records,
                            traits,
                            sum_types,
                        );
                        constrain_type_eq(
                            unifier,
                            &arg_ty,
                            &underlying_ty,
                            &prov(Reason::FunctionArg { param_index: 0 }),
                        );
                        return opaque_ty;
                    }

                    // Check user-defined sum types (with scoped constructor disambiguation)
                    if sum_types.has_variant(&name.node) {
                        // Extract expected sum type name from bidirectional hint.
                        let expected_type_name = unifier
                            .bidir_expected()
                            .and_then(|ty| match ty {
                                Type::Sum(st) => Some(st.name.clone()),
                                _ => None,
                            });
                        let resolution = sum_types.resolve_variant(
                            &name.node,
                            expected_type_name.as_deref(),
                        );
                        let (resolved_type_name, variant_info) = match resolution {
                            VariantResolution::Unique(tn, vi) => (tn, vi),
                            VariantResolution::Ambiguous(candidates) => {
                                unifier.push_error(
                                    Diagnostic::error(
                                        Category::TypeMismatch,
                                        format!(
                                            "ambiguous constructor `{}`",
                                            name.node,
                                        ),
                                    )
                                    .at(span_to_loc(name.span))
                                    .with_help(format!(
                                        "candidates: {}. Qualify with the type name: {}.{}(...)",
                                        candidates.iter().map(|c| format!("{c}.{}", name.node)).collect::<Vec<_>>().join(", "),
                                        candidates[0],
                                        name.node,
                                    )),
                                );
                                return unifier.fresh_type();
                            }
                            VariantResolution::NotFound => {
                                unreachable!("has_variant returned true but resolve_variant returned NotFound");
                            }
                        };
                        let has_named_fields =
                            variant_info.fields.iter().any(|field| field.name.is_some());
                        let expected_arity = variant_info.fields.len();

                        let Some(instantiated_variant) =
                            sum_types.instantiate_variant_for_type(
                                &name.node,
                                Some(&resolved_type_name),
                                unifier,
                            )
                        else {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::TypeMismatch,
                                    format!(
                                        "cannot instantiate constructor `{}` for type checking",
                                        name.node
                                    ),
                                )
                                .at(span_to_loc(name.span)),
                            );
                            return unifier.fresh_type();
                        };
                        // Record resolved type for evaluator dispatch.
                        unifier.record_resolved_variant(name.span, resolved_type_name.clone());

                        let mut ordered_args: Vec<Option<&Argument>> = vec![None; expected_arity];
                        let mut had_error = false;
                        if has_named_fields {
                            let label_to_idx: BTreeMap<&str, usize> = variant_info
                                .fields
                                .iter()
                                .enumerate()
                                .filter_map(|(idx, field)| {
                                    field.name.as_deref().map(|name| (name, idx))
                                })
                                .collect();
                            for arg in args {
                                let Some(label) = &arg.label else {
                                    had_error = true;
                                    unifier.push_error(
                                        Diagnostic::error(
                                            Category::ArityMismatch,
                                            format!(
                                                "constructor `{}` has named fields; use labeled arguments",
                                                name.node
                                            ),
                                        )
                                        .at(span_to_loc(arg.value.span)),
                                    );
                                    continue;
                                };
                                let Some(idx) = label_to_idx.get(label.node.as_str()).copied()
                                else {
                                    had_error = true;
                                    unifier.push_error(
                                        Diagnostic::error(
                                            Category::ArityMismatch,
                                            format!(
                                                "unknown field `{}` for constructor `{}`",
                                                label.node, name.node
                                            ),
                                        )
                                        .at(span_to_loc(label.span)),
                                    );
                                    continue;
                                };
                                if ordered_args[idx].is_some() {
                                    had_error = true;
                                    unifier.push_error(
                                        Diagnostic::error(
                                            Category::ArityMismatch,
                                            format!(
                                                "duplicate field `{}` in constructor `{}`",
                                                label.node, name.node
                                            ),
                                        )
                                        .at(span_to_loc(label.span)),
                                    );
                                    continue;
                                }
                                ordered_args[idx] = Some(arg);
                            }
                            for (idx, slot) in ordered_args.iter().enumerate() {
                                if slot.is_none() {
                                    had_error = true;
                                    let field_name = variant_info.fields[idx]
                                        .name
                                        .as_deref()
                                        .unwrap_or("<unknown>");
                                    unifier.push_error(
                                        Diagnostic::error(
                                            Category::ArityMismatch,
                                            format!(
                                                "missing field `{}` in constructor `{}`",
                                                field_name, name.node
                                            ),
                                        )
                                        .at(span_to_loc(expr.span)),
                                    );
                                }
                            }
                        } else {
                            if args.len() != expected_arity {
                                had_error = true;
                                unifier.push_error(
                                    Diagnostic::error(
                                        Category::ArityMismatch,
                                        format!(
                                            "`{}` expects {} argument{}, got {}",
                                            name.node,
                                            expected_arity,
                                            if expected_arity == 1 { "" } else { "s" },
                                            args.len(),
                                        ),
                                    )
                                    .at(span_to_loc(expr.span)),
                                );
                            }
                            for (idx, arg) in args.iter().take(expected_arity).enumerate() {
                                if arg.label.is_some() {
                                    had_error = true;
                                    unifier.push_error(
                                        Diagnostic::error(
                                            Category::ArityMismatch,
                                            format!(
                                                "constructor `{}` does not accept labeled arguments",
                                                name.node
                                            ),
                                        )
                                        .at(span_to_loc(arg.value.span)),
                                    );
                                }
                                ordered_args[idx] = Some(arg);
                            }
                        }

                        for (idx, (arg_opt, field_info)) in ordered_args
                            .iter()
                            .zip(instantiated_variant.field_types.iter())
                            .enumerate()
                        {
                            let Some(arg) = arg_opt else { continue };
                            let arg_ty = infer_expr_bidir(
                                &arg.value, env, unifier, records, traits, sum_types,
                            );
                            constrain_type_eq(
                                unifier,
                                &arg_ty,
                                &field_info.ty,
                                &prov(Reason::FunctionArg { param_index: idx }),
                            );
                        }
                        for (lhs, rhs) in instantiated_variant.where_constraints {
                            constrain_type_eq(unifier, &lhs, &rhs, &prov(Reason::PatternMatch));
                        }
                        if had_error {
                            return instantiated_variant.sum_type;
                        }
                        instantiated_variant.sum_type
                    } else {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::UndefinedName,
                                format!("unknown constructor `{}`", name.node),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                        unifier.fresh_type()
                    }
                }
            }
        }

        // -- Unary operators --
        ExprKind::UnaryOp { op, operand } => {
            let operand_ty = infer_expr_bidir(operand, env, unifier, records, traits, sum_types);
            match op.node {
                kea_ast::UnaryOp::Neg => {
                    // Negation: operand must be numeric, result is same type.
                    // We don't constrain to Int or Float specifically — the operand's
                    // own type determines it. If it's a type var, it stays polymorphic
                    // until something else constrains it.
                    operand_ty
                }
                kea_ast::UnaryOp::Not => {
                    // Logical not: operand must be Bool, result is Bool.
                    constrain_type_eq(
                        unifier,
                        &Type::Bool,
                        &operand_ty,
                        &prov(Reason::BinaryOp("not")),
                    );
                    Type::Bool
                }
            }
        }

        // -- Type ascription --
        ExprKind::As { expr, annotation } => {
            let ascribed_ty = match resolve_annotation_or_bare_df(
                &annotation.node,
                records,
                Some(sum_types),
                unifier,
            ) {
                Some(ty) => ty,
                None => {
                    push_annotation_resolution_error(
                        unifier,
                        &annotation.node,
                        annotation.span,
                        records,
                        Some(sum_types),
                    );
                    return unifier.fresh_type();
                }
            };
            check_expr_bidir(
                expr,
                &ascribed_ty,
                Reason::TypeAscription,
                env,
                unifier,
                records,
                traits,
                sum_types,
            );
            ascribed_ty
        }

        ExprKind::Use(_) => {
            unifier.push_error(
                Diagnostic::error(
                    Category::TypeError,
                    "`use` is a statement form and must appear in a block with a continuation",
                )
                .at(span_to_loc(expr.span)),
            );
            unifier.fresh_type()
        }

        ExprKind::Handle {
            expr: handled,
            clauses,
            then_clause,
        } => infer_handle_expr_type(
            expr.span,
            handled,
            clauses,
            then_clause.as_deref(),
            env,
            unifier,
            records,
            traits,
            sum_types,
        ),

        ExprKind::Resume { value } => {
            let value_ty = infer_expr_bidir(value, env, unifier, records, traits, sum_types);
            let Some(ctx) = env.current_resume_context() else {
                unifier.push_error(
                    Diagnostic::error(
                        Category::TypeError,
                        "`resume` is only valid inside a matching handler clause",
                    )
                    .at(span_to_loc(expr.span)),
                );
                return unifier.fresh_type();
            };

            constrain_type_eq(
                unifier,
                &value_ty,
                &ctx.operation_return,
                &Provenance {
                    span: value.span,
                    reason: Reason::TypeAscription,
                },
            );
            ctx.clause_result.clone()
        }

        // -- Case expression --
        ExprKind::Case { scrutinee, arms } => {
            let scrutinee_ty =
                infer_expr_bidir(scrutinee, env, unifier, records, traits, sum_types);

            let result_ty = unifier.fresh_type();
            let mut arm_reachability = Vec::with_capacity(arms.len());

            for arm in arms {
                let reachable =
                    pattern_reachable_for_case(&arm.pattern, &scrutinee_ty, sum_types, unifier);
                arm_reachability.push(reachable);
                if !reachable {
                    if let PatternKind::Constructor { name, .. } = &arm.pattern.node {
                        unifier.push_error(
                            Diagnostic::warning(
                                Category::TypeMismatch,
                                format!(
                                    "unreachable constructor arm `{name}` due to incompatible variant constraints"
                                ),
                            )
                            .at(span_to_loc(arm.pattern.span))
                            .with_help(
                                "remove the arm or relax the variant `where` constraints"
                                    .to_string(),
                            ),
                        );
                    }
                    continue;
                }

                // Constrain scrutinee shape globally without leaking branch-local
                // GADT equalities from variant where-clauses.
                constrain_case_pattern_shape(&arm.pattern, &scrutinee_ty, unifier, sum_types);

                let arm_scope = unifier.begin_scope();
                env.push_scope();
                infer_pattern(
                    &arm.pattern,
                    &scrutinee_ty,
                    env,
                    unifier,
                    records,
                    sum_types,
                );
                // Type-check guard in pattern's scope — must be Bool
                if let Some(ref guard) = arm.guard {
                    check_expr_bidir(
                        guard,
                        &Type::Bool,
                        Reason::CaseArms,
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                }
                check_expr_bidir(
                    &arm.body,
                    &result_ty,
                    Reason::CaseArms,
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
                env.pop_scope();

                let arm_result_ty = unifier.substitution.apply(&result_ty);
                unifier.end_scope(arm_scope, false);
                constrain_type_eq(
                    unifier,
                    &result_ty,
                    &arm_result_ty,
                    &Provenance {
                        span: arm.body.span,
                        reason: Reason::CaseArms,
                    },
                );
            }

            // Check exhaustiveness — guarded arms don't count as covering
            let patterns: Vec<&kea_ast::Pattern> = arms
                .iter()
                .zip(arm_reachability.iter())
                .filter(|arm| {
                    let (arm, reachable) = arm;
                    arm.guard.is_none() && **reachable
                })
                .map(|(arm, _)| &arm.pattern)
                .collect();
            let mut missing =
                crate::exhaustive::check_exhaustiveness(&scrutinee_ty, &patterns, unifier);
            if let Some(reachable_variants) =
                reachable_sum_variants_for_case(&scrutinee_ty, scrutinee.span, sum_types, unifier)
            {
                missing.retain(|variant| reachable_variants.contains(variant));
            }
            if !missing.is_empty() {
                let missing_str = missing.join(", ");
                unifier.push_error(
                    Diagnostic::error(
                        Category::NonExhaustive,
                        format!("non-exhaustive case expression, missing: {missing_str}"),
                    )
                    .at(span_to_loc(expr.span)),
                );
            }

            result_ty
        }

        // -- Cond expression --
        ExprKind::Cond { arms } => {
            let result_ty = unifier.fresh_type();
            let mut has_catch_all = false;

            for arm in arms {
                let mut arm_narrowings = ConditionNarrowings::default();
                if matches!(arm.condition.node, ExprKind::Wildcard) {
                    has_catch_all = true;
                } else {
                    arm_narrowings = check_condition_and_collect_narrowings(
                        &arm.condition,
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                }

                env.push_scope();
                apply_condition_narrowings(env, &arm_narrowings.true_bindings, unifier);
                check_expr_bidir(
                    &arm.body,
                    &result_ty,
                    Reason::CaseArms,
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
                env.pop_scope();
            }

            if !has_catch_all {
                unifier.push_error(
                    Diagnostic::error(
                        Category::NonExhaustive,
                        "non-exhaustive cond — add a _ -> ... catch-all",
                    )
                    .at(span_to_loc(expr.span)),
                );
            }

            result_ty
        }

        ExprKind::For(for_expr) => infer_for_expr(
            for_expr,
            env,
            unifier,
            records,
            traits,
            sum_types,
            ForInferContext { span: expr.span },
        ),

        // -- Map literal --
        ExprKind::MapLiteral(pairs) => {
            let key_ty = unifier.fresh_type();
            let val_ty = unifier.fresh_type();
            for (k, v) in pairs {
                let kt = infer_expr_bidir(k, env, unifier, records, traits, sum_types);
                let vt = infer_expr_bidir(v, env, unifier, records, traits, sum_types);
                constrain_type_eq(unifier, &key_ty, &kt, &prov(Reason::LetAnnotation));
                constrain_type_eq(unifier, &val_ty, &vt, &prov(Reason::LetAnnotation));
            }
            Type::Map(Box::new(key_ty), Box::new(val_ty))
        }

        ExprKind::Wildcard => {
            unifier.push_error(
                Diagnostic::error(
                    Category::Syntax,
                    "`_` is only valid as a cond catch-all arm condition",
                )
                .at(span_to_loc(expr.span)),
            );
            unifier.fresh_type()
        }

        // -- String interpolation --
        ExprKind::StringInterp(parts) => {
            for part in parts {
                if let kea_ast::StringInterpPart::Expr(expr) = part {
                    // Infer the expression type (any type is fine; displayed at runtime)
                    infer_expr_bidir(expr, env, unifier, records, traits, sum_types);
                }
            }
            Type::String
        }

        // Named record — not yet implemented.
        ExprKind::Record {
            name,
            fields,
            spread,
        } => {
            if records.lookup(&name.node).is_none() {
                unifier.push_error(
                    Diagnostic::error(
                        Category::UndefinedName,
                        format!("unknown record type `{}`", name.node),
                    )
                    .at(span_to_loc(name.span)),
                );
                return unifier.fresh_type();
            }

            // Build the expected record type
            let record_ty = records
                .to_type_with(&name.node, &mut Some(unifier))
                .expect("record was looked up");
            let record_row = match &record_ty {
                Type::Record(rec) => rec.row.clone(),
                _ => RowType::empty_closed(),
            };

            // Check for duplicate field names in construction
            {
                let mut seen: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
                for (field_name, _) in fields.iter() {
                    if !seen.insert(&field_name.node) {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::TypeMismatch,
                                format!(
                                    "duplicate field `{}` in record construction `{}`",
                                    field_name.node, name.node,
                                ),
                            )
                            .at(span_to_loc(field_name.span)),
                        );
                    }
                }
            }

            // Infer each provided field and collect them. When the record
            // declaration provides a field type, use checked mode so
            // precision literals (IntN/FloatN) get range diagnostics.
            let mut provided_fields: Vec<(Label, Type)> = Vec::new();
            for (field_name, field_expr) in fields {
                let label = Label::new(field_name.node.clone());
                let field_ty = if let Some((_, expected_field_ty)) = record_row
                    .fields
                    .iter()
                    .find(|(declared_label, _)| declared_label == &label)
                {
                    check_expr_bidir(
                        field_expr,
                        expected_field_ty,
                        Reason::RecordField {
                            label: label.clone(),
                        },
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    )
                } else {
                    infer_expr_bidir(field_expr, env, unifier, records, traits, sum_types)
                };
                provided_fields.push((label, field_ty));
            }

            // Validate each provided field's type against the record definition
            for (label, field_ty) in &provided_fields {
                if let Some((_, expected_field_ty)) = record_row
                    .fields
                    .iter()
                    .find(|(declared_label, _)| declared_label == label)
                {
                    constrain_type_eq(
                        unifier,
                        field_ty,
                        expected_field_ty,
                        &prov(Reason::RecordField {
                            label: label.clone(),
                        }),
                    );
                }
            }

            // Check for spread — if present, infer it and unify with the record type
            if let Some(spread_expr) = spread {
                let spread_ty =
                    infer_expr_bidir(spread_expr, env, unifier, records, traits, sum_types);
                constrain_type_eq(
                    unifier,
                    &spread_ty,
                    &record_ty,
                    &prov(Reason::RecordField {
                        label: Label::new(name.node.clone()),
                    }),
                );
            }

            if spread.is_none() {
                // Without spread, all fields must be provided
                let provided_row = RowType::closed(provided_fields);
                let provided_ty = Type::AnonRecord(provided_row);
                constrain_type_eq(
                    unifier,
                    &provided_ty,
                    &Type::AnonRecord(record_row.clone()),
                    &prov(Reason::RecordField {
                        label: Label::new(name.node.clone()),
                    }),
                );
            }

            record_ty
        }

        // -- Stream generator --
        ExprKind::StreamBlock { body, .. } => {
            let elem_ty = unifier.fresh_type();
            env.push_stream_context(elem_ty.clone());
            let _ = infer_expr_bidir(body, env, unifier, records, traits, sum_types);
            env.pop_stream_context();
            Type::Stream(Box::new(elem_ty))
        }

        ExprKind::Yield { value } => {
            let value_ty = infer_expr_bidir(value, env, unifier, records, traits, sum_types);
            if let Some(stream_elem_ty) = env.current_stream_context().cloned() {
                constrain_type_eq(
                    unifier,
                    &value_ty,
                    &stream_elem_ty,
                    &prov(Reason::LetAnnotation),
                );
            } else {
                unifier.push_error(
                    Diagnostic::error(
                        Category::TypeError,
                        "`yield` is only valid inside `stream { ... }`",
                    )
                    .at(span_to_loc(expr.span)),
                );
            }
            Type::Unit
        }

        ExprKind::YieldFrom { source } => {
            let source_ty = infer_expr_bidir(source, env, unifier, records, traits, sum_types);
            let yielded_ty = unifier.fresh_type();
            constrain_type_eq(
                unifier,
                &source_ty,
                &Type::Stream(Box::new(yielded_ty.clone())),
                &prov(Reason::FunctionArg { param_index: 0 }),
            );
            if let Some(stream_elem_ty) = env.current_stream_context().cloned() {
                constrain_type_eq(
                    unifier,
                    &yielded_ty,
                    &stream_elem_ty,
                    &prov(Reason::LetAnnotation),
                );
            } else {
                unifier.push_error(
                    Diagnostic::error(
                        Category::TypeError,
                        "`yield_from` is only valid inside `stream { ... }`",
                    )
                    .at(span_to_loc(expr.span)),
                );
            }
            Type::Unit
        }

        // -- Actor operations --
        ExprKind::Spawn {
            value: value_expr,
            config,
        } => {
            let inner_ty = infer_expr_bidir(value_expr, env, unifier, records, traits, sum_types);
            // Check Sendable: the value being spawned must be safe to transfer
            // across task boundaries. Apply current substitution to resolve what
            // we can — unresolved Var(_) is assumed Sendable (checked at resolution).
            let resolved = unifier.substitution.apply(&inner_ty);
            if !matches!(resolved, Type::Var(_)) {
                match resolve_sendable(traits, &resolved, unifier, value_expr.span) {
                    SendableSatisfaction::Satisfied => {}
                    SendableSatisfaction::Ambiguous => {}
                    SendableSatisfaction::Unsatisfied => {
                        let detail = sendable_violation(&resolved)
                            .map(|v| format!(": {}", v.reason))
                            .unwrap_or_default();
                        unifier.errors.push(
                            Diagnostic::error(
                                Category::TypeError,
                                format!(
                                    "value spawned as actor must be Sendable, but `{resolved}` is not{detail}",
                                ),
                            )
                            .at(span_to_loc(value_expr.span)),
                        );
                    }
                }
            }
            let spawn_kind = if matches!(resolved, Type::Var(_)) {
                SpawnKind::Task
            } else {
                match traits.solve_goal(&TraitGoal::Implements {
                    trait_name: "Actor".to_string(),
                    ty: resolved.clone(),
                }) {
                    SolveOutcome::Unique(_) | SolveOutcome::Ambiguous(_) => SpawnKind::Actor,
                    SolveOutcome::NoMatch(_) => SpawnKind::Task,
                }
            };

            // Type-check spawn config if present. Config applies only to Actor spawns.
            if let Some(cfg) = config {
                if !matches!(spawn_kind, SpawnKind::Actor) {
                    unifier.errors.push(
                        Diagnostic::error(
                            Category::TypeError,
                            "`spawn ... with { ... }` requires an Actor spawn target".to_string(),
                        )
                        .at(span_to_loc(expr.span)),
                    );
                }
                if let Some(expr) = &cfg.mailbox_size {
                    let ty = infer_expr_bidir(expr, env, unifier, records, traits, sum_types);
                    let resolved_ty = unifier.substitution.apply(&ty);
                    if matches!(resolved_ty, Type::Var(_)) {
                        constrain_type_eq(
                            unifier,
                            &ty,
                            &Type::Int,
                            &prov(Reason::FunctionArg { param_index: 0 }),
                        );
                    } else if !resolved_ty.is_integer() {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::TypeError,
                                format!(
                                    "`mailbox_size` must be an integer type, but got `{resolved_ty}`"
                                ),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                    }
                }
                if let Some(expr) = &cfg.max_restarts {
                    let ty = infer_expr_bidir(expr, env, unifier, records, traits, sum_types);
                    let resolved_ty = unifier.substitution.apply(&ty);
                    if matches!(resolved_ty, Type::Var(_)) {
                        constrain_type_eq(
                            unifier,
                            &ty,
                            &Type::Int,
                            &prov(Reason::FunctionArg { param_index: 0 }),
                        );
                    } else if !resolved_ty.is_integer() {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::TypeError,
                                format!(
                                    "`max_restarts` must be an integer type, but got `{resolved_ty}`"
                                ),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                    }
                }
                if let Some(expr) = &cfg.call_timeout {
                    let ty = infer_expr_bidir(expr, env, unifier, records, traits, sum_types);
                    let resolved_ty = unifier.substitution.apply(&ty);
                    if matches!(resolved_ty, Type::Var(_)) {
                        constrain_type_eq(
                            unifier,
                            &ty,
                            &Type::Int,
                            &prov(Reason::FunctionArg { param_index: 0 }),
                        );
                    } else if !resolved_ty.is_integer() {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::TypeError,
                                format!(
                                    "`call_timeout` must be an integer type, but got `{resolved_ty}`"
                                ),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                    }
                }
                if let Some(expr) = &cfg.supervision {
                    let ty = infer_expr_bidir(expr, env, unifier, records, traits, sum_types);
                    if let Some(supervision_ty) = sum_types.to_type("SupervisionAction") {
                        constrain_type_eq(
                            unifier,
                            &ty,
                            &supervision_ty,
                            &prov(Reason::FunctionArg { param_index: 0 }),
                        );
                    }
                }
            }
            unifier
                .type_annotations
                .spawn_kinds
                .insert(expr.span, spawn_kind);
            match spawn_kind {
                SpawnKind::Actor => Type::Actor(Box::new(inner_ty)),
                SpawnKind::Task => Type::Task(Box::new(inner_ty)),
            }
        }

        ExprKind::Await {
            expr: awaited,
            safe,
        } => {
            if env.in_actor_context() {
                unifier.push_error(
                    Diagnostic::warning(
                        Category::TypeError,
                        "await inside actor handler may cause deadlock",
                    )
                    .with_code("W0901")
                    .at(span_to_loc(expr.span))
                    .with_help(
                        "await blocks the actor mailbox; if the awaited task sends back to this actor, it can deadlock"
                            .to_string(),
                    ),
                );
            }
            let task_ty = infer_expr_bidir(awaited, env, unifier, records, traits, sum_types);
            let out = unifier.fresh_type();
            constrain_type_eq(
                unifier,
                &task_ty,
                &Type::Task(Box::new(out.clone())),
                &prov(Reason::ActorOp),
            );
            if *safe {
                Type::Result(
                    Box::new(out),
                    Box::new(
                        kea_types::builtin_error_sum_type("ActorError")
                            .expect("builtin ActorError sum type"),
                    ),
                )
            } else {
                out
            }
        }

        ExprKind::ActorSend {
            actor,
            method,
            args,
            safe,
        } => {
            let actor_ty = infer_expr_bidir(actor, env, unifier, records, traits, sum_types);
            // Infer and check Sendable on each argument
            let mut arg_types = Vec::new();
            for arg in args {
                let arg_ty = infer_expr_bidir(arg, env, unifier, records, traits, sum_types);
                let resolved_arg = unifier.substitution.apply(&arg_ty);
                if !matches!(resolved_arg, Type::Var(_)) {
                    match resolve_sendable(traits, &resolved_arg, unifier, arg.span) {
                        SendableSatisfaction::Satisfied => {}
                        SendableSatisfaction::Ambiguous => {}
                        SendableSatisfaction::Unsatisfied => {
                            let detail = sendable_violation(&resolved_arg)
                                .map(|v| format!(": {}", v.reason))
                                .unwrap_or_default();
                            unifier.errors.push(
                                Diagnostic::error(
                                    Category::TypeError,
                                    format!(
                                        "message argument must be Sendable, but `{resolved_arg}` is not{detail}",
                                    ),
                                )
                                .at(span_to_loc(arg.span)),
                            );
                        }
                    }
                }
                arg_types.push(resolved_arg);
            }
            // Unify actor type with Actor(T)
            let inner_var = unifier.fresh_type();
            constrain_type_eq(
                unifier,
                &actor_ty,
                &Type::Actor(Box::new(inner_var.clone())),
                &prov(Reason::ActorOp),
            );
            let resolved_inner = unifier.substitution.apply(&inner_var);
            // Method resolution against protocol
            if let Some(type_name) = type_name_for_trait_check(&resolved_inner)
                && let Some(protocol) = traits.find_actor_protocol(&type_name)
            {
                if let Some(mp) = protocol.methods.get(&method.node) {
                    // send/send? are only for Send semantics methods
                    if mp.semantics != DispatchSemantics::Send {
                        unifier.errors.push(
                            Diagnostic::error(
                                Category::TypeError,
                                format!(
                                    "method `{}` returns a value — use `call`/`call?` instead of `send`/`send?`",
                                    method.node,
                                ),
                            )
                            .at(span_to_loc(method.span)),
                        );
                    }
                    // Check argument count and types
                    if arg_types.len() != mp.params.len() {
                        unifier.errors.push(
                            Diagnostic::error(
                                Category::TypeError,
                                format!(
                                    "method `{}` expects {} argument(s), but {} were provided",
                                    method.node,
                                    mp.params.len(),
                                    arg_types.len(),
                                ),
                            )
                            .at(span_to_loc(method.span)),
                        );
                    } else {
                        for (i, (arg_ty, param_ty)) in arg_types.iter().zip(&mp.params).enumerate()
                        {
                            constrain_type_eq(
                                unifier,
                                arg_ty,
                                param_ty,
                                &prov(Reason::FunctionArg { param_index: i }),
                            );
                        }
                    }
                } else {
                    unifier.errors.push(
                        Diagnostic::error(
                            Category::TypeError,
                            format!("actor type `{type_name}` has no method `{}`", method.node,),
                        )
                        .at(span_to_loc(method.span)),
                    );
                }
            } else if let Some(type_name) = type_name_for_trait_check(&resolved_inner) {
                // Concrete type but no protocol registered — likely missing impl Actor
                unifier.errors.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!("actor type `{type_name}` has no registered protocol"),
                    )
                    .at(span_to_loc(actor.span)),
                );
            }
            // Type variables stay permissive — protocol resolves later
            if *safe {
                Type::Result(
                    Box::new(Type::Unit),
                    Box::new(
                        kea_types::builtin_error_sum_type("ActorError")
                            .expect("builtin ActorError sum type"),
                    ),
                )
            } else {
                Type::Unit
            }
        }

        ExprKind::ActorCall {
            actor,
            method,
            args,
            safe,
        } => {
            let actor_ty = infer_expr_bidir(actor, env, unifier, records, traits, sum_types);
            // Infer and check Sendable on each argument
            let mut arg_types = Vec::new();
            for arg in args {
                let arg_ty = infer_expr_bidir(arg, env, unifier, records, traits, sum_types);
                let resolved_arg = unifier.substitution.apply(&arg_ty);
                if !matches!(resolved_arg, Type::Var(_)) {
                    match resolve_sendable(traits, &resolved_arg, unifier, arg.span) {
                        SendableSatisfaction::Satisfied => {}
                        SendableSatisfaction::Ambiguous => {}
                        SendableSatisfaction::Unsatisfied => {
                            let detail = sendable_violation(&resolved_arg)
                                .map(|v| format!(": {}", v.reason))
                                .unwrap_or_default();
                            unifier.errors.push(
                                Diagnostic::error(
                                    Category::TypeError,
                                    format!(
                                        "message argument must be Sendable, but `{resolved_arg}` is not{detail}",
                                    ),
                                )
                                .at(span_to_loc(arg.span)),
                            );
                        }
                    }
                }
                arg_types.push(resolved_arg);
            }
            // Unify actor type with Actor(T)
            let inner_var = unifier.fresh_type();
            constrain_type_eq(
                unifier,
                &actor_ty,
                &Type::Actor(Box::new(inner_var.clone())),
                &prov(Reason::ActorOp),
            );
            let resolved_inner = unifier.substitution.apply(&inner_var);
            // Method resolution against protocol — `call` works on all methods
            let return_type = if let Some(type_name) = type_name_for_trait_check(&resolved_inner)
                && let Some(protocol) = traits.find_actor_protocol(&type_name)
            {
                if let Some(mp) = protocol.methods.get(&method.node) {
                    // Check argument count and types
                    if arg_types.len() != mp.params.len() {
                        unifier.errors.push(
                            Diagnostic::error(
                                Category::TypeError,
                                format!(
                                    "method `{}` expects {} argument(s), but {} were provided",
                                    method.node,
                                    mp.params.len(),
                                    arg_types.len(),
                                ),
                            )
                            .at(span_to_loc(method.span)),
                        );
                    } else {
                        for (i, (arg_ty, param_ty)) in arg_types.iter().zip(&mp.params).enumerate()
                        {
                            constrain_type_eq(
                                unifier,
                                arg_ty,
                                param_ty,
                                &prov(Reason::FunctionArg { param_index: i }),
                            );
                        }
                    }
                    // Return type depends on semantics:
                    // Send → Result(Unit, ActorError) (caller doesn't see new state)
                    // CallPure → Result(return_type, ActorError)
                    // CallWithState → Result(second_tuple_element, ActorError)
                    match mp.semantics {
                        DispatchSemantics::Send => Type::Unit,
                        DispatchSemantics::CallPure => mp.return_type.clone(),
                        DispatchSemantics::CallWithState => {
                            // return_type is #(Self, T), extract T
                            if let Type::Tuple(ref elems) = mp.return_type {
                                if elems.len() == 2 {
                                    elems[1].clone()
                                } else {
                                    mp.return_type.clone()
                                }
                            } else {
                                mp.return_type.clone()
                            }
                        }
                    }
                } else {
                    unifier.errors.push(
                        Diagnostic::error(
                            Category::TypeError,
                            format!("actor type `{type_name}` has no method `{}`", method.node,),
                        )
                        .at(span_to_loc(method.span)),
                    );
                    unifier.fresh_type()
                }
            } else if let Some(type_name) = type_name_for_trait_check(&resolved_inner) {
                // Concrete type but no protocol registered
                unifier.errors.push(
                    Diagnostic::error(
                        Category::TypeError,
                        format!("actor type `{type_name}` has no registered protocol"),
                    )
                    .at(span_to_loc(actor.span)),
                );
                unifier.fresh_type()
            } else {
                // Type variable — can't resolve protocol yet, stay permissive
                unifier.fresh_type()
            };
            if *safe {
                Type::Result(
                    Box::new(return_type),
                    Box::new(
                        kea_types::builtin_error_sum_type("ActorError")
                            .expect("builtin ActorError sum type"),
                    ),
                )
            } else {
                return_type
            }
        }

        ExprKind::ControlSend { actor, signal } => {
            let actor_ty = infer_expr_bidir(actor, env, unifier, records, traits, sum_types);
            let signal_ty = infer_expr_bidir(signal, env, unifier, records, traits, sum_types);

            // Check signal is Sendable
            let resolved_signal = unifier.substitution.apply(&signal_ty);
            if !matches!(resolved_signal, Type::Var(_)) {
                match resolve_sendable(traits, &resolved_signal, unifier, signal.span) {
                    SendableSatisfaction::Satisfied => {}
                    SendableSatisfaction::Ambiguous => {}
                    SendableSatisfaction::Unsatisfied => {
                        let detail = sendable_violation(&resolved_signal)
                            .map(|v| format!(": {}", v.reason))
                            .unwrap_or_default();
                        unifier.errors.push(
                            Diagnostic::error(
                                Category::TypeError,
                                format!(
                                    "control signal must be Sendable, but `{resolved_signal}` is not{detail}",
                                ),
                            )
                            .at(span_to_loc(signal.span)),
                        );
                    }
                }
            }

            // Unify actor type with Actor(T)
            let inner_var = unifier.fresh_type();
            constrain_type_eq(
                unifier,
                &actor_ty,
                &Type::Actor(Box::new(inner_var.clone())),
                &prov(Reason::ActorOp),
            );
            let resolved_inner = unifier.substitution.apply(&inner_var);

            // Check actor has a control channel and signal type matches
            if let Some(type_name) = type_name_for_trait_check(&resolved_inner)
                && let Some(protocol) = traits.find_actor_protocol(&type_name)
            {
                if let Some(ref ctrl_ty) = protocol.control_type {
                    constrain_type_eq(unifier, &signal_ty, ctrl_ty, &prov(Reason::ActorOp));
                } else {
                    unifier.errors.push(
                        Diagnostic::error(
                            Category::TypeError,
                            format!(
                                "actor type `{type_name}` does not have a control channel \
                                 (no `type Control = ...` in its `impl Actor` block)",
                            ),
                        )
                        .at(span_to_loc(expr.span)),
                    );
                }
            }
            Type::Unit
        }
    }
}

/// Check `expr` against an expected type.
///
/// This is the bidirectional check path: push expected types downward when
/// available, otherwise synthesize and constrain.
fn constrain_type_eq(
    unifier: &mut Unifier,
    expected: &Type,
    actual: &Type,
    provenance: &Provenance,
) {
    unifier.constrain(Constraint::TypeEqual {
        expected: expected.clone(),
        actual: actual.clone(),
        provenance: provenance.clone(),
    });
}

fn constrain_row_eq(
    unifier: &mut Unifier,
    expected: &RowType,
    actual: &RowType,
    provenance: &Provenance,
) {
    unifier.constrain(Constraint::RowEqual {
        expected: expected.clone(),
        actual: actual.clone(),
        provenance: provenance.clone(),
    });
}

fn constrain_lacks(unifier: &mut Unifier, var: RowVarId, label: Label, provenance: &Provenance) {
    unifier.constrain(Constraint::Lacks {
        var,
        label,
        provenance: provenance.clone(),
    });
}

fn constrain_trait_obligation(
    unifier: &mut Unifier,
    ty: &Type,
    trait_name: &str,
    provenance: &Provenance,
) {
    unifier.constrain(Constraint::TraitObligation {
        ty: ty.clone(),
        trait_name: trait_name.to_string(),
        provenance: provenance.clone(),
    });
}

fn constrain_kind_eq(
    unifier: &mut Unifier,
    expected: &Kind,
    actual: &Kind,
    provenance: &Provenance,
) {
    unifier.constrain(Constraint::KindEqual {
        expected: expected.clone(),
        actual: actual.clone(),
        provenance: provenance.clone(),
    });
}

enum PrecisionLiteralCompatibility {
    NotApplicable,
    Compatible(Type),
    Incompatible,
}

fn int_literal_fits_precision(
    value: i64,
    width: kea_types::IntWidth,
    signedness: kea_types::Signedness,
) -> bool {
    match (width, signedness) {
        (kea_types::IntWidth::I8, kea_types::Signedness::Signed) => i8::try_from(value).is_ok(),
        (kea_types::IntWidth::I16, kea_types::Signedness::Signed) => i16::try_from(value).is_ok(),
        (kea_types::IntWidth::I32, kea_types::Signedness::Signed) => i32::try_from(value).is_ok(),
        (kea_types::IntWidth::I64, kea_types::Signedness::Signed) => true,
        (kea_types::IntWidth::I8, kea_types::Signedness::Unsigned) => {
            value >= 0 && u8::try_from(value).is_ok()
        }
        (kea_types::IntWidth::I16, kea_types::Signedness::Unsigned) => {
            value >= 0 && u16::try_from(value).is_ok()
        }
        (kea_types::IntWidth::I32, kea_types::Signedness::Unsigned) => {
            value >= 0 && u32::try_from(value).is_ok()
        }
        // Parsed integer literals are currently i64-backed.
        (kea_types::IntWidth::I64, kea_types::Signedness::Unsigned) => value >= 0,
    }
}

fn float_literal_fits_precision(value: f64, width: kea_types::FloatWidth) -> bool {
    match width {
        kea_types::FloatWidth::F64 => value.is_finite(),
        kea_types::FloatWidth::F32 => value.is_finite() && value.abs() <= f32::MAX as f64,
        // IEEE 754 half precision max finite magnitude.
        kea_types::FloatWidth::F16 => value.is_finite() && value.abs() <= 65504.0,
    }
}

fn check_precision_literal_against_expected(
    expr: &Expr,
    expected: &Type,
    unifier: &mut Unifier,
    span: Span,
) -> PrecisionLiteralCompatibility {
    match (&expr.node, expected) {
        (ExprKind::Lit(Lit::Int(value)), Type::IntN(width, signedness)) => {
            if int_literal_fits_precision(*value, *width, *signedness) {
                PrecisionLiteralCompatibility::Compatible(expected.clone())
            } else {
                unifier.push_error(
                    Diagnostic::error(
                        Category::TypeMismatch,
                        format!("integer literal `{value}` does not fit in `{expected}`"),
                    )
                    .at(span_to_loc(span)),
                );
                PrecisionLiteralCompatibility::Incompatible
            }
        }
        (ExprKind::Lit(Lit::Float(value)), Type::FloatN(width)) => {
            if float_literal_fits_precision(*value, *width) {
                PrecisionLiteralCompatibility::Compatible(expected.clone())
            } else {
                unifier.push_error(
                    Diagnostic::error(
                        Category::TypeMismatch,
                        format!("float literal `{value}` is out of range for `{expected}`"),
                    )
                    .at(span_to_loc(span)),
                );
                PrecisionLiteralCompatibility::Incompatible
            }
        }
        _ => PrecisionLiteralCompatibility::NotApplicable,
    }
}

fn check_nominal_boundary(
    expected: &Type,
    actual: &Type,
    span: Span,
    unifier: &mut Unifier,
) {
    let resolved_expected = unifier.substitution.apply(expected);
    let resolved_actual = unifier.substitution.apply(actual);
    if let (Type::Record(rec), Type::AnonRecord(_)) = (&resolved_expected, &resolved_actual) {
        unifier.push_error(
            Diagnostic::error(
                Category::TypeMismatch,
                format!(
                    "type mismatch: expected {}, got anonymous record. \
                     Use `{} {{ ... }}` to construct a {}",
                    rec.name, rec.name, rec.name
                ),
            )
            .at(span_to_loc(span)),
        );
    }
}

fn constrain_type_eq_with_nominal_boundary(
    unifier: &mut Unifier,
    expected: &Type,
    actual: &Type,
    provenance: &Provenance,
) {
    check_nominal_boundary(expected, actual, provenance.span, unifier);
    constrain_type_eq(unifier, expected, actual, provenance);
}

#[allow(clippy::too_many_arguments)]
fn check_expr_bidir(
    expr: &Expr,
    expected: &Type,
    reason: Reason,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Type {
    match (&expr.node, expected) {
        (
            ExprKind::Lambda {
                params,
                body,
                return_annotation,
            },
            Type::Function(expected_fn),
        ) if params.len() == expected_fn.params.len() => {
            unifier.enter_lambda();
            env.push_scope();
            let param_types = expected_fn.params.clone();

            for (param, expected_param_ty) in params.iter().zip(expected_fn.params.iter()) {
                if let Some(ann) = &param.annotation {
                    if let Some(declared_ty) =
                        resolve_annotation_or_bare_df(&ann.node, records, Some(sum_types), unifier)
                    {
                        constrain_type_eq_with_nominal_boundary(
                            unifier,
                            expected_param_ty,
                            &declared_ty,
                            &Provenance {
                                span: ann.span,
                                reason: Reason::LetAnnotation,
                            },
                        );
                    } else if let Some((name, expected, got)) =
                        annotation_type_arity_mismatch(&ann.node, records, Some(sum_types))
                    {
                        push_annotation_arity_mismatch(unifier, ann.span, &name, expected, got);
                    }
                }

                match &param.pattern.node {
                    PatternKind::Var(name) => {
                        env.bind(name.clone(), TypeScheme::mono(expected_param_ty.clone()));
                    }
                    _ => {
                        if !pattern_is_irrefutable(&param.pattern) {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::NonExhaustive,
                                    "refutable pattern in function parameter; \
                                     use `case` inside the body for refutable patterns"
                                        .to_string(),
                                )
                                .at(span_to_loc(param.pattern.span)),
                            );
                        }
                        infer_pattern(
                            &param.pattern,
                            expected_param_ty,
                            env,
                            unifier,
                            records,
                            sum_types,
                        );
                    }
                }
            }

            let expected_ret = expected_fn.ret.as_ref().clone();
            if let Some(ann) = return_annotation {
                if let Some(declared_ret) =
                    resolve_annotation_or_bare_df(&ann.node, records, Some(sum_types), unifier)
                {
                    constrain_type_eq_with_nominal_boundary(
                        unifier,
                        &declared_ret,
                        &expected_ret,
                        &Provenance {
                            span: ann.span,
                            reason: Reason::LetAnnotation,
                        },
                    );
                    check_expr_bidir(
                        body,
                        &declared_ret,
                        Reason::LetAnnotation,
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                } else {
                    push_annotation_resolution_error(
                        unifier,
                        &ann.node,
                        ann.span,
                        records,
                        Some(sum_types),
                    );
                    check_expr_bidir(
                        body,
                        &expected_ret,
                        reason.clone(),
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                }
            } else {
                check_expr_bidir(
                    body,
                    &expected_ret,
                    reason.clone(),
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
            }

            env.pop_scope();
            unifier.exit_lambda();

            return Type::Function(FunctionType {
                params: param_types,
                ret: Box::new(expected_ret),
                effects: expected_fn.effects.clone(),
            });
        }
        (
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            },
            _,
        ) => {
            let narrowings = check_condition_and_collect_narrowings(
                condition, env, unifier, records, traits, sum_types,
            );
            env.push_scope();
            apply_condition_narrowings(env, &narrowings.true_bindings, unifier);
            check_expr_bidir(
                then_branch,
                expected,
                reason.clone(),
                env,
                unifier,
                records,
                traits,
                sum_types,
            );
            env.pop_scope();
            match else_branch {
                Some(else_expr) => {
                    env.push_scope();
                    apply_condition_narrowings(env, &narrowings.false_bindings, unifier);
                    check_expr_bidir(
                        else_expr,
                        expected,
                        reason.clone(),
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                    env.pop_scope();
                }
                None => {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::TypeError,
                            "internal error: `if` without `else` reached type checker",
                        )
                        .at(span_to_loc(expr.span)),
                    );
                }
            }
            return expected.clone();
        }
        (ExprKind::Case { scrutinee, arms }, _) => {
            let scrutinee_ty =
                infer_expr_bidir(scrutinee, env, unifier, records, traits, sum_types);
            let mut arm_reachability = Vec::with_capacity(arms.len());

            for arm in arms {
                let reachable =
                    pattern_reachable_for_case(&arm.pattern, &scrutinee_ty, sum_types, unifier);
                arm_reachability.push(reachable);
                if !reachable {
                    if let PatternKind::Constructor { name, .. } = &arm.pattern.node {
                        unifier.push_error(
                            Diagnostic::warning(
                                Category::TypeMismatch,
                                format!(
                                    "unreachable constructor arm `{name}` due to incompatible variant constraints"
                                ),
                            )
                            .at(span_to_loc(arm.pattern.span))
                            .with_help(
                                "remove the arm or relax the variant `where` constraints"
                                    .to_string(),
                            ),
                        );
                    }
                    continue;
                }

                constrain_case_pattern_shape(&arm.pattern, &scrutinee_ty, unifier, sum_types);

                let arm_scope = unifier.begin_scope();
                env.push_scope();
                infer_pattern(
                    &arm.pattern,
                    &scrutinee_ty,
                    env,
                    unifier,
                    records,
                    sum_types,
                );
                if let Some(ref guard) = arm.guard {
                    check_expr_bidir(
                        guard,
                        &Type::Bool,
                        Reason::CaseArms,
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                }
                check_expr_bidir(
                    &arm.body,
                    expected,
                    reason.clone(),
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
                env.pop_scope();
                unifier.end_scope(arm_scope, false);
            }

            let patterns: Vec<&kea_ast::Pattern> = arms
                .iter()
                .zip(arm_reachability.iter())
                .filter(|arm| {
                    let (arm, reachable) = arm;
                    arm.guard.is_none() && **reachable
                })
                .map(|(arm, _)| &arm.pattern)
                .collect();
            let mut missing =
                crate::exhaustive::check_exhaustiveness(&scrutinee_ty, &patterns, unifier);
            if let Some(reachable_variants) =
                reachable_sum_variants_for_case(&scrutinee_ty, scrutinee.span, sum_types, unifier)
            {
                missing.retain(|variant| reachable_variants.contains(variant));
            }
            if !missing.is_empty() {
                let missing_str = missing.join(", ");
                unifier.push_error(
                    Diagnostic::error(
                        Category::NonExhaustive,
                        format!("non-exhaustive case expression, missing: {missing_str}"),
                    )
                    .at(span_to_loc(expr.span)),
                );
            }
            return expected.clone();
        }
        (ExprKind::Cond { arms }, _) => {
            let mut has_catch_all = false;

            for arm in arms {
                let mut arm_narrowings = ConditionNarrowings::default();
                if matches!(arm.condition.node, ExprKind::Wildcard) {
                    has_catch_all = true;
                } else {
                    arm_narrowings = check_condition_and_collect_narrowings(
                        &arm.condition,
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                }

                env.push_scope();
                apply_condition_narrowings(env, &arm_narrowings.true_bindings, unifier);
                check_expr_bidir(
                    &arm.body,
                    expected,
                    reason.clone(),
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
                env.pop_scope();
            }

            if !has_catch_all {
                unifier.push_error(
                    Diagnostic::error(
                        Category::NonExhaustive,
                        "non-exhaustive cond — add a _ -> ... catch-all",
                    )
                    .at(span_to_loc(expr.span)),
                );
            }
            return expected.clone();
        }
        (ExprKind::BinaryOp { op, left, right }, _)
            if matches!(
                op.node,
                BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Mod
                    | BinOp::Concat
                    | BinOp::Combine
            ) =>
        {
            let op_name = binop_name(op.node);
            let left_ty = check_expr_bidir(
                left,
                expected,
                Reason::BinaryOp(op_name),
                env,
                unifier,
                records,
                traits,
                sum_types,
            );
            let right_ty = check_expr_bidir(
                right,
                expected,
                Reason::BinaryOp(op_name),
                env,
                unifier,
                records,
                traits,
                sum_types,
            );
            constrain_type_eq_with_nominal_boundary(
                unifier,
                &left_ty,
                &right_ty,
                &Provenance {
                    span: expr.span,
                    reason: Reason::BinaryOp(op_name),
                },
            );
            let resolved_expected = unifier.substitution.apply(expected);
            // Each operator dispatches through its own trait:
            // `+` → Additive (numeric + Duration, not String)
            // `++` → Concatenable (String, List, Seq)
            // `<>` → Monoid (generic combine)
            // `-`, `*`, `/`, `%` → numeric
            let (trait_name, fallback_numeric): (&str, bool) = match op.node {
                BinOp::Add => ("Additive", true),
                BinOp::Concat => ("Concatenable", false),
                BinOp::Combine => ("Monoid", false),
                _ => ("", true),
            };
            let type_ok = matches!(resolved_expected, Type::Var(_) | Type::Dynamic)
                || if !trait_name.is_empty()
                    && traits.lookup_trait(trait_name).is_some()
                {
                    matches!(
                        traits.solve_goal(&TraitGoal::Implements {
                            trait_name: trait_name.to_string(),
                            ty: resolved_expected.clone(),
                        }),
                        SolveOutcome::Unique(_)
                    )
                } else if fallback_numeric {
                    resolved_expected.is_numeric()
                } else {
                    false
                };
            if !type_ok {
                let required = match op.node {
                    BinOp::Add => "Additive",
                    BinOp::Concat => "Concatenable",
                    BinOp::Combine => "Monoid",
                    _ => "numeric",
                };
                unifier.push_error(
                    Diagnostic::error(
                        Category::TypeMismatch,
                        format!(
                            "operator `{op_name}` requires {required} type, got `{resolved_expected}`"
                        ),
                    )
                    .at(span_to_loc(expr.span)),
                );
            }
            return unifier.substitution.apply(&left_ty);
        }
        (ExprKind::UnaryOp { op, operand }, _) => match op.node {
            kea_ast::UnaryOp::Neg => {
                check_expr_bidir(
                    operand,
                    expected,
                    Reason::BinaryOp("-"),
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
                let resolved_expected = unifier.substitution.apply(expected);
                if !matches!(resolved_expected, Type::Var(_) | Type::Dynamic)
                    && !resolved_expected.is_numeric()
                {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::TypeMismatch,
                            format!("operator `-` expects numeric type, got `{resolved_expected}`"),
                        )
                        .at(span_to_loc(expr.span)),
                    );
                }
                return expected.clone();
            }
            kea_ast::UnaryOp::Not => {
                check_expr_bidir(
                    operand,
                    &Type::Bool,
                    Reason::BinaryOp("not"),
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
                constrain_type_eq_with_nominal_boundary(
                    unifier,
                    expected,
                    &Type::Bool,
                    &Provenance {
                        span: expr.span,
                        reason: Reason::BinaryOp("not"),
                    },
                );
                return Type::Bool;
            }
        },
        (
            ExprKind::As {
                expr: inner,
                annotation,
            },
            _,
        ) => {
            if let Some(ascribed_ty) =
                resolve_annotation_or_bare_df(&annotation.node, records, Some(sum_types), unifier)
            {
                check_expr_bidir(
                    inner,
                    &ascribed_ty,
                    Reason::TypeAscription,
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
                constrain_type_eq_with_nominal_boundary(
                    unifier,
                    expected,
                    &ascribed_ty,
                    &Provenance {
                        span: expr.span,
                        reason: reason.clone(),
                    },
                );
                return ascribed_ty;
            }
        }
        (ExprKind::FieldAccess { expr: obj, field }, _)
            if field.node != "value"
                && !matches!(
                    &obj.node,
                    ExprKind::Var(module_name)
                        if env.lookup(module_name).is_none() && looks_like_module_name(module_name)
                ) =>
        {
            let label = Label::new(field.node.clone());
            let rest = unifier.fresh_row_var();
            let required_obj_ty =
                Type::AnonRecord(RowType::open(vec![(label.clone(), expected.clone())], rest));
            check_expr_bidir(
                obj,
                &required_obj_ty,
                Reason::RecordField {
                    label: label.clone(),
                },
                env,
                unifier,
                records,
                traits,
                sum_types,
            );
            return expected.clone();
        }
        (ExprKind::Tuple(elems), Type::Tuple(expected_elems))
            if elems.len() == expected_elems.len() =>
        {
            for (idx, (elem, expected_elem_ty)) in
                elems.iter().zip(expected_elems.iter()).enumerate()
            {
                check_expr_bidir(
                    elem,
                    expected_elem_ty,
                    Reason::FunctionArg { param_index: idx },
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
            }
            return expected.clone();
        }
        (ExprKind::List(elems), Type::List(expected_elem_ty)) => {
            for (idx, elem) in elems.iter().enumerate() {
                check_expr_bidir(
                    elem,
                    expected_elem_ty,
                    Reason::FunctionArg { param_index: idx },
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
            }
            return expected.clone();
        }
        (ExprKind::MapLiteral(pairs), Type::Map(expected_key_ty, expected_val_ty)) => {
            for (idx, (key_expr, value_expr)) in pairs.iter().enumerate() {
                check_expr_bidir(
                    key_expr,
                    expected_key_ty,
                    Reason::FunctionArg {
                        param_index: idx * 2,
                    },
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
                check_expr_bidir(
                    value_expr,
                    expected_val_ty,
                    Reason::FunctionArg {
                        param_index: idx * 2 + 1,
                    },
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );
            }
            return expected.clone();
        }
        (ExprKind::AnonRecord { fields, spread }, Type::AnonRecord(expected_row)) => {
            let mut seen_labels = BTreeSet::new();
            let mut field_types = Vec::with_capacity(fields.len());
            for (name, field_expr) in fields {
                if !seen_labels.insert(name.node.clone()) {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::TypeMismatch,
                            format!("duplicate field `{}` in anonymous record", name.node),
                        )
                        .at(span_to_loc(name.span)),
                    );
                }

                let label = Label::new(name.node.clone());
                let field_ty = if let Some((_, expected_field_ty)) = expected_row
                    .fields
                    .iter()
                    .find(|(expected_label, _)| expected_label == &label)
                {
                    check_expr_bidir(
                        field_expr,
                        expected_field_ty,
                        Reason::RecordField {
                            label: label.clone(),
                        },
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    )
                } else {
                    infer_expr_bidir(field_expr, env, unifier, records, traits, sum_types)
                };
                field_types.push((label, field_ty));
            }

            let actual = if let Some(spread_expr) = spread {
                let spread_ty =
                    infer_expr_bidir(spread_expr, env, unifier, records, traits, sum_types);
                let tail = unifier.fresh_row_var();
                for (label, _) in &field_types {
                    constrain_lacks(
                        unifier,
                        tail,
                        label.clone(),
                        &Provenance {
                            span: expr.span,
                            reason: Reason::RowExtension {
                                label: label.clone(),
                            },
                        },
                    );
                }
                let spread_row = RowType::open(vec![], tail);
                constrain_type_eq_with_nominal_boundary(
                    unifier,
                    &spread_ty,
                    &Type::AnonRecord(spread_row),
                    &Provenance {
                        span: expr.span,
                        reason: Reason::RecordField {
                            label: Label::new("..spread".to_string()),
                        },
                    },
                );
                Type::AnonRecord(RowType::open(field_types, tail))
            } else {
                Type::AnonRecord(RowType::closed(field_types))
            };

            constrain_type_eq_with_nominal_boundary(
                unifier,
                expected,
                &actual,
                &Provenance {
                    span: expr.span,
                    reason: reason.clone(),
                },
            );
            return expected.clone();
        }
        (ExprKind::Constructor { name, args }, Type::Option(inner_expected)) => {
            match name.node.as_str() {
                "Some" => {
                    if args.len() != 1 {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                format!("`Some` expects 1 argument, got {}", args.len()),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                        return expected.clone();
                    }
                    if args[0].label.is_some() {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                "`Some` does not accept labeled arguments",
                            )
                            .at(span_to_loc(args[0].value.span)),
                        );
                    }
                    check_expr_bidir(
                        &args[0].value,
                        inner_expected,
                        Reason::FunctionArg { param_index: 0 },
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                    return expected.clone();
                }
                "None" => {
                    if !args.is_empty() {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                format!("`None` expects 0 arguments, got {}", args.len()),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                    }
                    return expected.clone();
                }
                _ => {}
            }
        }
        (ExprKind::Constructor { name, args }, Type::Result(ok_expected, err_expected)) => {
            match name.node.as_str() {
                "Ok" => {
                    if args.len() != 1 {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                format!("`Ok` expects 1 argument, got {}", args.len()),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                        return expected.clone();
                    }
                    if args[0].label.is_some() {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                "`Ok` does not accept labeled arguments",
                            )
                            .at(span_to_loc(args[0].value.span)),
                        );
                    }
                    check_expr_bidir(
                        &args[0].value,
                        ok_expected,
                        Reason::FunctionArg { param_index: 0 },
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                    return expected.clone();
                }
                "Err" => {
                    if args.len() != 1 {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                format!("`Err` expects 1 argument, got {}", args.len()),
                            )
                            .at(span_to_loc(expr.span)),
                        );
                        return expected.clone();
                    }
                    if args[0].label.is_some() {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                "`Err` does not accept labeled arguments",
                            )
                            .at(span_to_loc(args[0].value.span)),
                        );
                    }
                    check_expr_bidir(
                        &args[0].value,
                        err_expected,
                        Reason::FunctionArg { param_index: 0 },
                        env,
                        unifier,
                        records,
                        traits,
                        sum_types,
                    );
                    return expected.clone();
                }
                _ => {}
            }
        }
        (ExprKind::Call { func, args }, _) => {
            let (call_signature, bound_args) =
                resolve_bound_call_args(func, args, expr.span, env, unifier);
            let func_ty = infer_expr_bidir(func, env, unifier, records, traits, sum_types);
            let callable_ty = instantiate_callable_type_for_call(&func_ty, unifier, expr.span);
            let resolved_callable = unifier.substitution.apply(&callable_ty);
            if let Type::Function(ft) = &resolved_callable
                && ft.params.len() == bound_args.len()
            {
                let arg_types = infer_bound_args_with_param_contracts(
                    &bound_args,
                    call_signature.as_ref(),
                    Some(&ft.params),
                    env,
                    unifier,
                    records,
                    traits,
                    sum_types,
                );

                constrain_type_eq_with_nominal_boundary(
                    unifier,
                    expected,
                    &ft.ret,
                    &Provenance {
                        span: expr.span,
                        reason: Reason::FunctionArg { param_index: 0 },
                    },
                );
                unifier.note_evidence_site(expr.span, &callable_ty);
                note_existential_pack_sites(unifier, expr.span, &callable_ty, &arg_types);
                return expected.clone();
            }
        }
        (ExprKind::Block(exprs), _) => {
            if exprs.is_empty() {
                constrain_type_eq_with_nominal_boundary(
                    unifier,
                    expected,
                    &Type::Unit,
                    &Provenance {
                        span: expr.span,
                        reason: reason.clone(),
                    },
                );
                return Type::Unit;
            }
            env.push_scope();
            let mut idx = 0usize;
            while idx + 1 < exprs.len() {
                let current = &exprs[idx];
                if let ExprKind::Use(_) = &current.node {
                    let actual =
                        infer_use_chain_expr(exprs, idx, env, unifier, records, traits, sum_types);
                    constrain_type_eq_with_nominal_boundary(
                        unifier,
                        expected,
                        &actual,
                        &Provenance {
                            span: current.span,
                            reason: reason.clone(),
                        },
                    );
                    env.pop_scope();
                    return actual;
                }
                infer_expr_bidir(current, env, unifier, records, traits, sum_types);
                idx += 1;
            }
            let tail = exprs
                .last()
                .expect("non-empty block should have a final expression");
            let actual = check_expr_bidir(
                tail,
                expected,
                reason.clone(),
                env,
                unifier,
                records,
                traits,
                sum_types,
            );
            env.pop_scope();
            return actual;
        }
        _ => {}
    }

    // Set bidirectional expected type hint for constructor disambiguation.
    let prev_bidir = unifier.bidir_expected().cloned();
    unifier.set_bidir_expected(Some(expected.clone()));
    let actual = infer_expr_bidir(expr, env, unifier, records, traits, sum_types);
    unifier.set_bidir_expected(prev_bidir);

    // Bidirectional subsumption fallback for polymorphic expectations:
    // when the expected type is `forall`, prefer a scheme-level probe before
    // falling back to first-order unification on instantiated types.
    if let Type::Forall(expected_scheme) = expected
        && let Some(actual_scheme) = poly_scheme_from_argument_expr(expr, &actual, env, unifier)
    {
        let mut probe = unifier.clone();
        let expected_ty = skolemize_poly_scheme(expected_scheme);
        let actual_ty = instantiate(&actual_scheme, &mut probe);
        if probe.constraints_satisfiable(vec![Constraint::TypeEqual {
            expected: expected_ty,
            actual: actual_ty,
            provenance: Provenance {
                span: expr.span,
                reason: reason.clone(),
            },
        }]) {
            return actual;
        }
    }

    match check_precision_literal_against_expected(expr, expected, unifier, expr.span) {
        PrecisionLiteralCompatibility::Compatible(lit_ty) => lit_ty,
        PrecisionLiteralCompatibility::Incompatible => actual,
        PrecisionLiteralCompatibility::NotApplicable => {
            constrain_type_eq_with_nominal_boundary(
                unifier,
                expected,
                &actual,
                &Provenance {
                    span: expr.span,
                    reason,
                },
            );
            actual
        }
    }
}

fn variant_constraints_satisfiable(
    probe_unifier: &Unifier,
    sum_type: Type,
    where_constraints: Vec<(Type, Type)>,
    actual_scrutinee: Type,
    provenance: Provenance,
) -> bool {
    let mut constraints = vec![Constraint::TypeEqual {
        expected: sum_type,
        actual: actual_scrutinee,
        provenance: provenance.clone(),
    }];
    for (lhs, rhs) in where_constraints {
        constraints.push(Constraint::TypeEqual {
            expected: lhs,
            actual: rhs,
            provenance: provenance.clone(),
        });
    }
    probe_unifier.constraints_satisfiable(constraints)
}

fn reachable_sum_variants_for_case(
    scrutinee_ty: &Type,
    scrutinee_span: Span,
    sum_types: &SumTypeRegistry,
    unifier: &mut Unifier,
) -> Option<BTreeSet<String>> {
    let resolved_scrutinee = unifier.substitution.apply(scrutinee_ty);
    let Type::Sum(st) = resolved_scrutinee else {
        return None;
    };
    let info = sum_types.lookup(&st.name)?;
    if info
        .variants
        .iter()
        .all(|variant| variant.where_constraints.is_empty())
    {
        return None;
    }

    let mut reachable = BTreeSet::new();
    let resolved_scrutinee = unifier.substitution.apply(scrutinee_ty);
    for variant in &info.variants {
        let mut probe_unifier = unifier.clone();
        if let Some(instantiated_variant) =
            sum_types.instantiate_variant_for_type(&variant.name, Some(&st.name), &mut probe_unifier)
        {
            let provenance = Provenance {
                span: scrutinee_span,
                reason: Reason::PatternMatch,
            };
            if variant_constraints_satisfiable(
                &probe_unifier,
                instantiated_variant.sum_type,
                instantiated_variant.where_constraints,
                resolved_scrutinee.clone(),
                provenance,
            ) {
                reachable.insert(variant.name.clone());
            }
        }
    }

    Some(reachable)
}

fn pattern_reachable_for_case(
    pattern: &kea_ast::Pattern,
    scrutinee_ty: &Type,
    sum_types: &SumTypeRegistry,
    unifier: &mut Unifier,
) -> bool {
    let PatternKind::Constructor { name, .. } = &pattern.node else {
        return true;
    };
    if !sum_types.has_variant(name) {
        return true;
    }
    let resolved_scrutinee_ty = unifier.substitution.apply(scrutinee_ty);
    let expected_type_name = match &resolved_scrutinee_ty {
        Type::Sum(st) => Some(st.name.as_str()),
        _ => None,
    };
    let mut probe_unifier = unifier.clone();
    let Some(instantiated_variant) = sum_types.instantiate_variant_for_type(
        name,
        expected_type_name,
        &mut probe_unifier,
    ) else {
        return true;
    };

    let provenance = Provenance {
        span: pattern.span,
        reason: Reason::PatternMatch,
    };
    variant_constraints_satisfiable(
        &probe_unifier,
        instantiated_variant.sum_type,
        instantiated_variant.where_constraints,
        unifier.substitution.apply(scrutinee_ty),
        provenance,
    )
}

fn constrain_case_pattern_shape(
    pattern: &kea_ast::Pattern,
    expected_ty: &Type,
    unifier: &mut Unifier,
    sum_types: &SumTypeRegistry,
) {
    let prov = Provenance {
        span: pattern.span,
        reason: Reason::PatternMatch,
    };

    match &pattern.node {
        PatternKind::Wildcard | PatternKind::Var(_) => {}
        PatternKind::Lit(lit) => {
            let lit_ty = match lit {
                Lit::Int(_) => Type::Int,
                Lit::Float(_) => Type::Float,
                Lit::Bool(_) => Type::Bool,
                Lit::String(_) => Type::String,
                Lit::Unit => Type::Unit,
            };
            constrain_type_eq(unifier, &lit_ty, expected_ty, &prov);
        }
        PatternKind::Constructor { name, args, .. } => match name.as_str() {
            "Some" => {
                let inner_ty = unifier.fresh_type();
                let option_ty = Type::Option(Box::new(inner_ty.clone()));
                constrain_type_eq(unifier, &option_ty, expected_ty, &prov);
                if let [inner_pat] = args.as_slice() {
                    constrain_case_pattern_shape(&inner_pat.pattern, &inner_ty, unifier, sum_types);
                }
            }
            "None" => {
                let inner_ty = unifier.fresh_type();
                let option_ty = Type::Option(Box::new(inner_ty));
                constrain_type_eq(unifier, &option_ty, expected_ty, &prov);
            }
            "Ok" => {
                let ok_ty = unifier.fresh_type();
                let err_ty = unifier.fresh_type();
                let result_ty = Type::Result(Box::new(ok_ty.clone()), Box::new(err_ty));
                constrain_type_eq(unifier, &result_ty, expected_ty, &prov);
                if let [ok_pat] = args.as_slice() {
                    constrain_case_pattern_shape(&ok_pat.pattern, &ok_ty, unifier, sum_types);
                }
            }
            "Err" => {
                let ok_ty = unifier.fresh_type();
                let err_ty = unifier.fresh_type();
                let result_ty = Type::Result(Box::new(ok_ty), Box::new(err_ty.clone()));
                constrain_type_eq(unifier, &result_ty, expected_ty, &prov);
                if let [err_pat] = args.as_slice() {
                    constrain_case_pattern_shape(&err_pat.pattern, &err_ty, unifier, sum_types);
                }
            }
            _ => {
                // Use scrutinee type for disambiguation.
                let resolved_expected = unifier.substitution.apply(expected_ty);
                let expected_type_name = match &resolved_expected {
                    Type::Sum(st) => Some(st.name.as_str()),
                    _ => None,
                };
                let Some(instantiated_variant) = sum_types.instantiate_variant_for_type(
                    name,
                    expected_type_name,
                    unifier,
                ) else {
                    return;
                };
                // Shape-only constraint: do not apply variant where-constraints here.
                constrain_type_eq(unifier, &instantiated_variant.sum_type, expected_ty, &prov);
                let has_named_fields = instantiated_variant
                    .field_types
                    .iter()
                    .any(|field| field.name.is_some());
                if has_named_fields {
                    let field_index: BTreeMap<&str, usize> = instantiated_variant
                        .field_types
                        .iter()
                        .enumerate()
                        .filter_map(|(idx, field)| field.name.as_deref().map(|name| (name, idx)))
                        .collect();
                    for arg in args {
                        let resolved_name = if let Some(name) = &arg.name {
                            Some(name.node.clone())
                        } else if let PatternKind::Var(var_name) = &arg.pattern.node {
                            Some(var_name.clone())
                        } else {
                            None
                        };
                        let Some(field_name) = resolved_name else {
                            continue;
                        };
                        let Some(idx) = field_index.get(field_name.as_str()).copied() else {
                            continue;
                        };
                        constrain_case_pattern_shape(
                            &arg.pattern,
                            &instantiated_variant.field_types[idx].ty,
                            unifier,
                            sum_types,
                        );
                    }
                } else {
                    for (arg_pat, field_ty) in
                        args.iter().zip(instantiated_variant.field_types.iter())
                    {
                        constrain_case_pattern_shape(
                            &arg_pat.pattern,
                            &field_ty.ty,
                            unifier,
                            sum_types,
                        );
                    }
                }
            }
        },
        PatternKind::Tuple(items) => {
            let elem_tys: Vec<Type> = items.iter().map(|_| unifier.fresh_type()).collect();
            constrain_type_eq(unifier, &Type::Tuple(elem_tys.clone()), expected_ty, &prov);
            for (item, elem_ty) in items.iter().zip(elem_tys.iter()) {
                constrain_case_pattern_shape(item, elem_ty, unifier, sum_types);
            }
        }
        PatternKind::AnonRecord { .. } | PatternKind::Record { .. } => {
            // Record-pattern shape constraints are not conjunctively safe across arms.
        }
        PatternKind::Or(_) => {
            // Disjunctive shape constraints are handled by arm-local checking.
        }
        PatternKind::As { pattern: inner, .. } => {
            constrain_case_pattern_shape(inner, expected_ty, unifier, sum_types);
        }
        PatternKind::List { elements, rest } => {
            let elem_ty = unifier.fresh_type();
            constrain_type_eq(unifier, &Type::List(Box::new(elem_ty.clone())), expected_ty, &prov);
            for elem in elements {
                constrain_case_pattern_shape(elem, &elem_ty, unifier, sum_types);
            }
            if let Some(rest_pat) = rest {
                let rest_ty = Type::List(Box::new(elem_ty));
                constrain_case_pattern_shape(rest_pat, &rest_ty, unifier, sum_types);
            }
        }
    }
}

fn looks_like_module_name(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_uppercase)
}

enum SendableSatisfaction {
    Satisfied,
    Unsatisfied,
    Ambiguous,
}

fn resolve_sendable(
    traits: &TraitRegistry,
    ty: &Type,
    unifier: &mut Unifier,
    span: Span,
) -> SendableSatisfaction {
    if traits.lookup_trait("Sendable").is_some() {
        match solve_trait_impl_with_diag(traits, unifier, "Sendable", ty, span) {
            SolveOutcome::Unique(_) => SendableSatisfaction::Satisfied,
            SolveOutcome::Ambiguous(_) => SendableSatisfaction::Ambiguous,
            SolveOutcome::NoMatch(_) => {
                if is_sendable(ty) {
                    SendableSatisfaction::Satisfied
                } else {
                    SendableSatisfaction::Unsatisfied
                }
            }
        }
    } else if is_sendable(ty) {
        SendableSatisfaction::Satisfied
    } else {
        SendableSatisfaction::Unsatisfied
    }
}

/// Infer the type constraints imposed by a pattern and bind pattern variables.
///
/// Each pattern variable is bound as a monomorphic type in the current scope.
/// The pattern structure is unified with `expected_ty` (the scrutinee type).
fn infer_pattern(
    pattern: &kea_ast::Pattern,
    expected_ty: &Type,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    sum_types: &SumTypeRegistry,
) {
    let prov = Provenance {
        span: pattern.span,
        reason: Reason::PatternMatch,
    };

    match &pattern.node {
        PatternKind::Wildcard => {
            // No binding, no constraint.
        }

        PatternKind::Var(name) => {
            env.bind(name.clone(), TypeScheme::mono(expected_ty.clone()));
        }

        PatternKind::Lit(lit) => {
            let lit_ty = match lit {
                Lit::Int(_) => Type::Int,
                Lit::Float(_) => Type::Float,
                Lit::Bool(_) => Type::Bool,
                Lit::String(_) => Type::String,
                Lit::Unit => Type::Unit,
            };
            constrain_type_eq(unifier, &lit_ty, expected_ty, &prov);
        }

        PatternKind::Constructor { name, qualifier, args, rest } => match name.as_str() {
            "Some" => {
                if *rest {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::Syntax,
                            "`..` is not allowed in `Some` patterns",
                        )
                        .at(span_to_loc(pattern.span)),
                    );
                }
                if args.len() != 1 {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::ArityMismatch,
                            format!("`{name}` expects 1 argument in pattern, got {}", args.len()),
                        )
                        .at(span_to_loc(pattern.span)),
                    );
                }
                let inner_ty = unifier.fresh_type();
                let option_ty = Type::Option(Box::new(inner_ty.clone()));
                constrain_type_eq(unifier, &option_ty, expected_ty, &prov);
                if args.len() == 1 {
                    if args[0].name.is_some() {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                "`Some` pattern does not accept named fields",
                            )
                            .at(span_to_loc(pattern.span)),
                        );
                    }
                    infer_pattern(
                        &args[0].pattern,
                        &inner_ty,
                        env,
                        unifier,
                        records,
                        sum_types,
                    );
                }
            }
            "None" => {
                if *rest {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::Syntax,
                            "`..` is not allowed in `None` patterns",
                        )
                        .at(span_to_loc(pattern.span)),
                    );
                }
                if !args.is_empty() {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::ArityMismatch,
                            format!(
                                "`{name}` expects 0 arguments in pattern, got {}",
                                args.len()
                            ),
                        )
                        .at(span_to_loc(pattern.span)),
                    );
                }
                let inner_ty = unifier.fresh_type();
                let option_ty = Type::Option(Box::new(inner_ty));
                constrain_type_eq(unifier, &option_ty, expected_ty, &prov);
            }
            "Ok" => {
                if *rest {
                    unifier.push_error(
                        Diagnostic::error(Category::Syntax, "`..` is not allowed in `Ok` patterns")
                            .at(span_to_loc(pattern.span)),
                    );
                }
                if args.len() != 1 {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::ArityMismatch,
                            format!("`{name}` expects 1 argument in pattern, got {}", args.len()),
                        )
                        .at(span_to_loc(pattern.span)),
                    );
                }
                let ok_ty = unifier.fresh_type();
                let err_ty = unifier.fresh_type();
                let result_ty = Type::Result(Box::new(ok_ty.clone()), Box::new(err_ty));
                constrain_type_eq(unifier, &result_ty, expected_ty, &prov);
                if args.len() == 1 {
                    if args[0].name.is_some() {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                "`Ok` pattern does not accept named fields",
                            )
                            .at(span_to_loc(pattern.span)),
                        );
                    }
                    infer_pattern(&args[0].pattern, &ok_ty, env, unifier, records, sum_types);
                }
            }
            "Err" => {
                if *rest {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::Syntax,
                            "`..` is not allowed in `Err` patterns",
                        )
                        .at(span_to_loc(pattern.span)),
                    );
                }
                if args.len() != 1 {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::ArityMismatch,
                            format!("`{name}` expects 1 argument in pattern, got {}", args.len()),
                        )
                        .at(span_to_loc(pattern.span)),
                    );
                }
                let ok_ty = unifier.fresh_type();
                let err_ty = unifier.fresh_type();
                let result_ty = Type::Result(Box::new(ok_ty), Box::new(err_ty.clone()));
                constrain_type_eq(unifier, &result_ty, expected_ty, &prov);
                if args.len() == 1 {
                    if args[0].name.is_some() {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                "`Err` pattern does not accept named fields",
                            )
                            .at(span_to_loc(pattern.span)),
                        );
                    }
                    infer_pattern(&args[0].pattern, &err_ty, env, unifier, records, sum_types);
                }
            }
            _ => {
                if let Some(info) = records.lookup_opaque(name) {
                    if *rest {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::Syntax,
                                "`..` is not allowed in opaque constructor patterns",
                            )
                            .at(span_to_loc(pattern.span)),
                        );
                    }
                    if args.len() != 1 {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::ArityMismatch,
                                format!("`{name}` expects 1 argument in pattern"),
                            )
                            .at(span_to_loc(pattern.span)),
                        );
                        return;
                    }
                    let params: Vec<Type> =
                        info.params.iter().map(|_| unifier.fresh_type()).collect();
                    let opaque_ty = Type::Opaque {
                        name: name.clone(),
                        params: params.clone(),
                    };
                    constrain_type_eq(unifier, &opaque_ty, expected_ty, &prov);
                    if let Some(underlying_ty) =
                        instantiate_opaque_target(name, &params, records, Some(sum_types))
                    {
                        if args[0].name.is_some() {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::ArityMismatch,
                                    "opaque constructor pattern does not accept named fields",
                                )
                                .at(span_to_loc(pattern.span)),
                            );
                        }
                        infer_pattern(
                            &args[0].pattern,
                            &underlying_ty,
                            env,
                            unifier,
                            records,
                            sum_types,
                        );
                    } else {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::TypeMismatch,
                                format!("cannot resolve underlying type for opaque `{name}`"),
                            )
                            .at(span_to_loc(pattern.span)),
                        );
                    }
                    return;
                }

                // Check user-defined sum types (with scoped constructor disambiguation)
                if qualifier.is_some() || sum_types.has_variant(name) {
                    // If qualifier is present, use it directly; otherwise disambiguate
                    let resolution = if let Some(qual) = qualifier {
                        // Qualified: Type.Variant — look up directly
                        if let Some(info) = sum_types.lookup_variant_in_type(name, qual) {
                            VariantResolution::Unique(qual.clone(), info.clone())
                        } else {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::UndefinedName,
                                    format!("type `{qual}` has no variant `{name}`"),
                                )
                                .at(span_to_loc(pattern.span)),
                            );
                            return;
                        }
                    } else {
                        // In pattern position, the scrutinee type provides the expected type.
                        let resolved_expected = unifier.substitution.apply(expected_ty);
                        let expected_type_name = match &resolved_expected {
                            Type::Sum(st) => Some(st.name.as_str()),
                            _ => None,
                        };
                        sum_types.resolve_variant(name, expected_type_name)
                    };
                    let resolved_type_name = match resolution {
                        VariantResolution::Unique(tn, _) => tn,
                        VariantResolution::Ambiguous(candidates) => {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::TypeMismatch,
                                    format!("ambiguous constructor `{name}` in pattern"),
                                )
                                .at(span_to_loc(pattern.span))
                                .with_help(format!(
                                    "candidates: {}. Qualify with the type name: {}.{name}(...)",
                                    candidates.iter().map(|c| format!("{c}.{name}")).collect::<Vec<_>>().join(", "),
                                    candidates[0],
                                )),
                            );
                            return;
                        }
                        VariantResolution::NotFound => {
                            // Not a known variant.
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::UndefinedName,
                                    format!("unknown constructor `{name}`"),
                                )
                                .at(span_to_loc(pattern.span)),
                            );
                            return;
                        }
                    };
                    let Some(instantiated_variant) = sum_types.instantiate_variant_for_type(
                        name,
                        Some(&resolved_type_name),
                        unifier,
                    ) else {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::TypeMismatch,
                                format!("cannot instantiate constructor `{name}` in pattern"),
                            )
                            .at(span_to_loc(pattern.span)),
                        );
                        return;
                    };
                    unifier.record_resolved_variant(pattern.span, resolved_type_name);
                    constrain_type_eq(unifier, &instantiated_variant.sum_type, expected_ty, &prov);
                    for (lhs, rhs) in instantiated_variant.where_constraints {
                        constrain_type_eq(unifier, &lhs, &rhs, &prov);
                    }
                    let has_named_fields = instantiated_variant
                        .field_types
                        .iter()
                        .any(|field| field.name.is_some());
                    if has_named_fields {
                        let field_index: BTreeMap<&str, usize> = instantiated_variant
                            .field_types
                            .iter()
                            .enumerate()
                            .filter_map(|(idx, field)| {
                                field.name.as_deref().map(|name| (name, idx))
                            })
                            .collect();
                        let mut assigned: Vec<Option<&kea_ast::Pattern>> =
                            vec![None; instantiated_variant.field_types.len()];
                        for arg in args {
                            let resolved_name = if let Some(name) = &arg.name {
                                Some(name.node.clone())
                            } else if let PatternKind::Var(var_name) = &arg.pattern.node {
                                Some(var_name.clone())
                            } else {
                                None
                            };
                            let Some(field_name) = resolved_name else {
                                unifier.push_error(
                                    Diagnostic::error(
                                        Category::ArityMismatch,
                                        format!(
                                            "named constructor pattern `{name}` requires `field: pattern` or identifier punning",
                                        ),
                                    )
                                    .at(span_to_loc(arg.pattern.span)),
                                );
                                continue;
                            };
                            let Some(idx) = field_index.get(field_name.as_str()).copied() else {
                                unifier.push_error(
                                    Diagnostic::error(
                                        Category::ArityMismatch,
                                        format!(
                                            "unknown field `{field_name}` in constructor pattern `{name}`",
                                        ),
                                    )
                                    .at(span_to_loc(arg.pattern.span)),
                                );
                                continue;
                            };
                            if assigned[idx].is_some() {
                                unifier.push_error(
                                    Diagnostic::error(
                                        Category::ArityMismatch,
                                        format!(
                                            "duplicate field `{field_name}` in constructor pattern `{name}`",
                                        ),
                                    )
                                    .at(span_to_loc(arg.pattern.span)),
                                );
                                continue;
                            }
                            assigned[idx] = Some(&arg.pattern);
                        }
                        if !*rest {
                            for (idx, slot) in assigned.iter().enumerate() {
                                if slot.is_none() {
                                    let field_name = instantiated_variant.field_types[idx]
                                        .name
                                        .as_deref()
                                        .unwrap_or("<unknown>");
                                    unifier.push_error(
                                        Diagnostic::error(
                                            Category::ArityMismatch,
                                            format!(
                                                "missing field `{field_name}` in constructor pattern `{name}`",
                                            ),
                                        )
                                        .at(span_to_loc(pattern.span)),
                                    );
                                }
                            }
                        }
                        for (idx, pat) in assigned.into_iter().enumerate() {
                            let Some(pat) = pat else { continue };
                            infer_pattern(
                                pat,
                                &instantiated_variant.field_types[idx].ty,
                                env,
                                unifier,
                                records,
                                sum_types,
                            );
                        }
                    } else {
                        if *rest {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::Syntax,
                                    format!(
                                        "`..` is only allowed in constructor patterns with named fields (`{name}` is positional)",
                                    ),
                                )
                                .at(span_to_loc(pattern.span)),
                            );
                        }
                        if args.len() != instantiated_variant.field_types.len() {
                            unifier.push_error(
                                Diagnostic::error(
                                    Category::ArityMismatch,
                                    format!(
                                        "`{name}` expects {} argument{} in pattern, got {}",
                                        instantiated_variant.field_types.len(),
                                        if instantiated_variant.field_types.len() == 1 {
                                            ""
                                        } else {
                                            "s"
                                        },
                                        args.len()
                                    ),
                                )
                                .at(span_to_loc(pattern.span)),
                            );
                        }
                        for (arg, field_ty) in
                            args.iter().zip(instantiated_variant.field_types.iter())
                        {
                            if arg.name.is_some() {
                                unifier.push_error(
                                    Diagnostic::error(
                                        Category::ArityMismatch,
                                        format!(
                                            "constructor pattern `{name}` does not accept named fields",
                                        ),
                                    )
                                    .at(span_to_loc(arg.pattern.span)),
                                );
                            }
                            infer_pattern(
                                &arg.pattern,
                                &field_ty.ty,
                                env,
                                unifier,
                                records,
                                sum_types,
                            );
                        }
                    }
                } else {
                    unifier.push_error(
                        Diagnostic::error(
                            Category::UndefinedName,
                            format!("unknown constructor `{name}` in pattern"),
                        )
                        .at(span_to_loc(pattern.span)),
                    );
                }
            }
        },

        PatternKind::Tuple(pats) => {
            let elem_types: Vec<Type> = pats.iter().map(|_| unifier.fresh_type()).collect();
            let tuple_ty = Type::Tuple(elem_types.clone());
            constrain_type_eq(unifier, &tuple_ty, expected_ty, &prov);
            for (pat, ty) in pats.iter().zip(elem_types.iter()) {
                infer_pattern(pat, ty, env, unifier, records, sum_types);
            }
        }

        // Anonymous record pattern: #{ name, age } or #{ name, .. }
        PatternKind::AnonRecord { fields, rest } => {
            let field_types: Vec<(Label, Type)> = fields
                .iter()
                .map(|(name, pat)| {
                    let field_ty = unifier.fresh_type();
                    infer_pattern(pat, &field_ty, env, unifier, records, sum_types);
                    (Label::new(name.clone()), field_ty)
                })
                .collect();
            let row = if *rest {
                let tail = unifier.fresh_row_var();
                RowType::open(field_types, tail)
            } else {
                RowType::closed(field_types)
            };
            let prov = Provenance {
                span: pattern.span,
                reason: Reason::PatternMatch,
            };
            constrain_type_eq(unifier, expected_ty, &Type::AnonRecord(row), &prov);
        }

        PatternKind::Record { name, fields, rest } => {
            if records.lookup(name).is_none() {
                unifier.push_error(
                    Diagnostic::error(
                        Category::UndefinedName,
                        format!("unknown record type `{name}`"),
                    )
                    .at(span_to_loc(pattern.span)),
                );
                return;
            }

            let record_ty = records
                .to_type_with(name, &mut Some(unifier))
                .expect("record was looked up");
            let record_row = match &record_ty {
                Type::Record(rec) => rec.row.clone(),
                _ => RowType::empty_closed(),
            };

            // Unify the expected type with the nominal record type
            let prov = Provenance {
                span: pattern.span,
                reason: Reason::PatternMatch,
            };
            constrain_type_eq(unifier, expected_ty, &record_ty, &prov);

            // Bind each field pattern against the record's declared field types
            let field_types: Vec<(Label, Type)> = fields
                .iter()
                .map(|(field_name, pat)| {
                    let field_ty = unifier.fresh_type();
                    infer_pattern(pat, &field_ty, env, unifier, records, sum_types);
                    (Label::new(field_name.clone()), field_ty)
                })
                .collect();

            // Unify the pattern's structural row against the record's row directly
            let pattern_row = if *rest {
                let tail = unifier.fresh_row_var();
                RowType::open(field_types, tail)
            } else {
                RowType::closed(field_types)
            };
            constrain_row_eq(unifier, &pattern_row, &record_row, &prov);
        }

        PatternKind::Or(alternatives) => {
            // All alternatives must match the same type and bind the same set of names.
            // Use collect_pattern_bindings from kea_ast to check consistency.
            let mut first_bindings: Option<Vec<String>> = None;
            for alt in alternatives {
                let mut names = std::collections::HashSet::new();
                kea_ast::collect_pattern_bindings_pub(&alt.node, &mut names);
                let mut sorted: Vec<String> = names.into_iter().collect();
                sorted.sort();

                if let Some(ref first) = first_bindings {
                    if *first != sorted {
                        unifier.push_error(
                            Diagnostic::error(
                                Category::TypeMismatch,
                                format!(
                                    "or-pattern alternatives bind different names: {{{}}} vs {{{}}}",
                                    first.join(", "),
                                    sorted.join(", "),
                                ),
                            )
                            .at(span_to_loc(alt.span)),
                        );
                    }
                } else {
                    first_bindings = Some(sorted);
                }

                // Type-check each alternative against the expected type
                env.push_scope();
                infer_pattern(alt, expected_ty, env, unifier, records, sum_types);
                env.pop_scope();
            }
            // Bind the names from the first alternative (they're all the same)
            if let Some(first_alt) = alternatives.first() {
                infer_pattern(first_alt, expected_ty, env, unifier, records, sum_types);
            }
        }

        PatternKind::As {
            pattern: inner,
            name,
        } => {
            // Bind the whole value to name, then infer the inner pattern
            env.bind(name.node.clone(), TypeScheme::mono(expected_ty.clone()));
            infer_pattern(inner, expected_ty, env, unifier, records, sum_types);
        }

        PatternKind::List { elements, rest } => {
            let elem_ty = unifier.fresh_type();
            let list_ty = Type::List(Box::new(elem_ty.clone()));
            constrain_type_eq(unifier, &list_ty, expected_ty, &prov);
            for elem_pat in elements {
                infer_pattern(elem_pat, &elem_ty, env, unifier, records, sum_types);
            }
            if let Some(rest_pat) = rest {
                let rest_ty = Type::List(Box::new(elem_ty));
                infer_pattern(rest_pat, &rest_ty, env, unifier, records, sum_types);
            }
        }
    }
}

fn binop_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Concat => "++",
        BinOp::Combine => "<>",
        BinOp::Eq => "==",
        BinOp::Neq => "!=",
        BinOp::Lt => "<",
        BinOp::Lte => "<=",
        BinOp::Gt => ">",
        BinOp::Gte => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::In => "in",
        BinOp::NotIn => "not in",
    }
}

/// Build an ActorProtocol from a type's actor impl methods.
///
/// **Precondition**: `methods` must contain concrete (monomorphic, nominal) types,
/// not generalized types from the type environment. Use [`concrete_method_types_from_decls`]
/// to build suitable input from FnDecl annotations.
///
/// Each method type should be a resolved `Function { params: [Self, ...], ret: R }`.
/// The first parameter (`self`) is stripped; dispatch semantics are derived from the
/// return type relative to the type name.
/// Config methods: evaluated once at spawn time, NOT included in the dispatch table.
/// These provide trait-level defaults for actor configuration.
pub const ACTOR_CONFIG_METHODS: &[&str] = &[
    "mailbox_size",
    "supervision",
    "max_restarts",
    "tick_interval",
];

/// Lifecycle methods: included in the dispatch table but excluded from the send/call protocol.
/// These are dispatched internally (init on spawn/restart, terminate on exit,
/// handle_control on control channel) but not callable by users via send/call.
pub const ACTOR_LIFECYCLE_METHODS: &[&str] = &["init", "on_tick", "handle_control", "terminate"];

pub fn build_actor_protocol(
    type_name: &str,
    methods: &BTreeMap<String, Type>,
    control_type: Option<Type>,
) -> ActorProtocol {
    let mut protocol_methods = BTreeMap::new();

    for (name, ty) in methods {
        // Skip config and lifecycle methods — they're not user-callable dispatch targets.
        if ACTOR_CONFIG_METHODS.contains(&name.as_str())
            || ACTOR_LIFECYCLE_METHODS.contains(&name.as_str())
        {
            continue;
        }
        if let Type::Function(ft) = ty {
            // Strip self parameter (first param)
            let params = if ft.params.is_empty() {
                vec![]
            } else {
                ft.params[1..].to_vec()
            };
            let semantics = derive_dispatch_semantics(type_name, &ft.ret);
            protocol_methods.insert(
                name.clone(),
                MethodProtocol {
                    params,
                    return_type: (*ft.ret).clone(),
                    semantics,
                },
            );
        }
    }

    ActorProtocol {
        type_name: type_name.to_string(),
        methods: protocol_methods,
        control_type,
    }
}

/// Resolve a type annotation with `Self` mapping to a concrete type.
///
/// Wraps [`resolve_annotation`] with an additional check: if the annotation
/// is `Named("Self")`, returns the `self_type` instead of looking up "Self"
/// in the record registry (which would fail).
fn resolve_annotation_with_self(
    ann: &TypeAnnotation,
    records: &RecordRegistry,
    self_type: &Type,
) -> Option<Type> {
    resolve_annotation_with_self_and_assoc(ann, records, self_type, &BTreeMap::new())
}

/// Resolve a type annotation with `Self` and associated types in scope.
///
/// `Self` maps to `self_type`. `Self.Name` resolves via `assoc_types`.
fn resolve_annotation_with_self_and_assoc(
    ann: &TypeAnnotation,
    records: &RecordRegistry,
    self_type: &Type,
    assoc_types: &BTreeMap<String, Type>,
) -> Option<Type> {
    match ann {
        TypeAnnotation::Named(name) if name == "Self" => Some(self_type.clone()),
        TypeAnnotation::Projection { base, name } if base == "Self" => {
            assoc_types.get(name).cloned()
        }
        TypeAnnotation::Applied(name, args) => {
            if let Some(op_ty) = eval_record_type_op(name, args, |arg_ann| {
                resolve_annotation_with_self_and_assoc(arg_ann, records, self_type, assoc_types)
            }) {
                return Some(op_ty);
            }
            if builtin_arity_mismatch(name, args.len()).is_some() {
                return None;
            }
            if name == "Decimal" {
                return resolve_decimal_annotation(args);
            }
            match (name.as_str(), args.as_slice()) {
                ("Option", [inner]) => Some(Type::Option(Box::new(
                    resolve_annotation_with_self_and_assoc(inner, records, self_type, assoc_types)?,
                ))),
                ("Result", [ok, err]) => Some(Type::Result(
                    Box::new(resolve_annotation_with_self_and_assoc(
                        ok,
                        records,
                        self_type,
                        assoc_types,
                    )?),
                    Box::new(resolve_annotation_with_self_and_assoc(
                        err,
                        records,
                        self_type,
                        assoc_types,
                    )?),
                )),
                ("List", [inner]) => Some(Type::List(Box::new(
                    resolve_annotation_with_self_and_assoc(inner, records, self_type, assoc_types)?,
                ))),
                ("Map", [key, val]) => Some(Type::Map(
                    Box::new(resolve_annotation_with_self_and_assoc(
                        key,
                        records,
                        self_type,
                        assoc_types,
                    )?),
                    Box::new(resolve_annotation_with_self_and_assoc(
                        val,
                        records,
                        self_type,
                        assoc_types,
                    )?),
                )),
                ("Set", [inner]) => Some(Type::Set(Box::new(
                    resolve_annotation_with_self_and_assoc(inner, records, self_type, assoc_types)?,
                ))),
                ("Actor", [inner]) => Some(Type::Actor(Box::new(
                    resolve_annotation_with_self_and_assoc(inner, records, self_type, assoc_types)?,
                ))),
                ("Arc", [inner]) => Some(Type::Arc(Box::new(
                    resolve_annotation_with_self_and_assoc(inner, records, self_type, assoc_types)?,
                ))),
                ("Stream", [inner]) => Some(Type::Stream(Box::new(
                    resolve_annotation_with_self_and_assoc(inner, records, self_type, assoc_types)?,
                ))),
                ("Task", [inner]) => Some(Type::Task(Box::new(
                    resolve_annotation_with_self_and_assoc(inner, records, self_type, assoc_types)?,
                ))),
                ("Tagged", [inner_ann]) => Some(Type::Tagged {
                    inner: Box::new(resolve_annotation_with_self_and_assoc(
                        inner_ann, records, self_type, assoc_types,
                    )?),
                    tags: BTreeMap::new(),
                }),
                _ => resolve_named_type_application(name, args, records, None, |arg_ann| {
                    resolve_annotation_with_self_and_assoc(arg_ann, records, self_type, assoc_types)
                }),
            }
        }
        TypeAnnotation::Tuple(elems) => {
            let resolved: Vec<Type> = elems
                .iter()
                .map(|elem| {
                    resolve_annotation_with_self_and_assoc(elem, records, self_type, assoc_types)
                })
                .collect::<Option<Vec<_>>>()?;
            Some(Type::Tuple(resolved))
        }
        TypeAnnotation::Function(params, ret) => {
            let resolved_params: Vec<Type> = params
                .iter()
                .map(|param| {
                    resolve_annotation_with_self_and_assoc(param, records, self_type, assoc_types)
                })
                .collect::<Option<Vec<_>>>()?;
            let resolved_ret =
                resolve_annotation_with_self_and_assoc(ret, records, self_type, assoc_types)?;
            Some(Type::Function(FunctionType {
                params: resolved_params,
                ret: Box::new(resolved_ret),
                effects: EffectRow::pure(),
            }))
        }
        TypeAnnotation::FunctionWithEffect(params, effect, ret) => {
            let resolved_params: Vec<Type> = params
                .iter()
                .map(|param| {
                    resolve_annotation_with_self_and_assoc(param, records, self_type, assoc_types)
                })
                .collect::<Option<Vec<_>>>()?;
            let resolved_ret =
                resolve_annotation_with_self_and_assoc(ret, records, self_type, assoc_types)?;
            let effects = effect_annotation_to_compat_row(&effect.node, Some(records))
                .unwrap_or_else(pure_effect_row);
            Some(Type::Function(FunctionType {
                params: resolved_params,
                ret: Box::new(resolved_ret),
                effects,
            }))
        }
        TypeAnnotation::Optional(inner) => {
            let resolved =
                resolve_annotation_with_self_and_assoc(inner, records, self_type, assoc_types)?;
            Some(Type::Option(Box::new(resolved)))
        }
        TypeAnnotation::Existential {
            bounds,
            associated_types,
        } => {
            let resolved_assoc: Option<BTreeMap<String, Type>> = associated_types
                .iter()
                .map(|(name, ann)| {
                    resolve_annotation_with_self_and_assoc(ann, records, self_type, assoc_types)
                        .map(|ty| (name.clone(), ty))
                })
                .collect();
            Some(Type::Existential {
                bounds: bounds.clone(),
                associated_types: resolved_assoc?,
            })
        }
        _ => resolve_annotation(ann, records, None),
    }
}

/// Resolve a type annotation with `Self`, associated types, and in-scope
/// type-parameter placeholders (including constructor-kinded parameters).
///
/// `type_params` is a mutable map so lower-case type variables (for example
/// `a`, `b`) can be interned on first use and reused across a single method
/// signature.
fn resolve_annotation_with_self_assoc_and_params(
    ann: &TypeAnnotation,
    records: &RecordRegistry,
    self_type: &Type,
    assoc_types: &BTreeMap<String, Type>,
    type_params: &mut BTreeMap<String, Type>,
    placeholder_id: &mut u32,
) -> Option<Type> {
    match ann {
        TypeAnnotation::Named(name) if name == "Self" => Some(self_type.clone()),
        TypeAnnotation::Projection { base, name } if base == "Self" => {
            assoc_types.get(name).cloned()
        }
        TypeAnnotation::Named(name) => {
            if let Some(ty) = type_params.get(name) {
                return Some(ty.clone());
            }
            if let Some(ty) = resolve_annotation(ann, records, None) {
                return Some(ty);
            }
            if looks_like_type_var_name(name) {
                *placeholder_id = placeholder_id.wrapping_sub(1);
                let tv = Type::Var(TypeVarId(*placeholder_id));
                type_params.insert(name.clone(), tv.clone());
                return Some(tv);
            }
            None
        }
        TypeAnnotation::Applied(name, args) => {
            if let Some(constructor_ty) = type_params.get(name).cloned() {
                let resolved_args: Option<Vec<_>> = args
                    .iter()
                    .map(|arg_ann| {
                        resolve_annotation_with_self_assoc_and_params(
                            arg_ann,
                            records,
                            self_type,
                            assoc_types,
                            type_params,
                            placeholder_id,
                        )
                    })
                    .collect();
                return Some(Type::App(Box::new(constructor_ty), resolved_args?));
            }

            if looks_like_type_var_name(name) {
                *placeholder_id = placeholder_id.wrapping_sub(1);
                let ctor = Type::Var(TypeVarId(*placeholder_id));
                type_params.insert(name.clone(), ctor.clone());
                let resolved_args: Option<Vec<_>> = args
                    .iter()
                    .map(|arg_ann| {
                        resolve_annotation_with_self_assoc_and_params(
                            arg_ann,
                            records,
                            self_type,
                            assoc_types,
                            type_params,
                            placeholder_id,
                        )
                    })
                    .collect();
                return Some(Type::App(Box::new(ctor), resolved_args?));
            }

            if let Some(op_ty) = eval_record_type_op(name, args, |arg_ann| {
                resolve_annotation_with_self_assoc_and_params(
                    arg_ann,
                    records,
                    self_type,
                    assoc_types,
                    type_params,
                    placeholder_id,
                )
            }) {
                return Some(op_ty);
            }
            if builtin_arity_mismatch(name, args.len()).is_some() {
                return None;
            }
            if name == "Decimal" {
                return resolve_decimal_annotation(args);
            }
            match (name.as_str(), args.as_slice()) {
                ("Option", [inner]) => Some(Type::Option(Box::new(
                    resolve_annotation_with_self_assoc_and_params(
                        inner,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?,
                ))),
                ("Result", [ok, err]) => Some(Type::Result(
                    Box::new(resolve_annotation_with_self_assoc_and_params(
                        ok,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?),
                    Box::new(resolve_annotation_with_self_assoc_and_params(
                        err,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?),
                )),
                ("List", [inner]) => Some(Type::List(Box::new(
                    resolve_annotation_with_self_assoc_and_params(
                        inner,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?,
                ))),
                ("Map", [key, val]) => Some(Type::Map(
                    Box::new(resolve_annotation_with_self_assoc_and_params(
                        key,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?),
                    Box::new(resolve_annotation_with_self_assoc_and_params(
                        val,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?),
                )),
                ("Set", [inner]) => Some(Type::Set(Box::new(
                    resolve_annotation_with_self_assoc_and_params(
                        inner,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?,
                ))),
                ("Actor", [inner]) => Some(Type::Actor(Box::new(
                    resolve_annotation_with_self_assoc_and_params(
                        inner,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?,
                ))),
                ("Arc", [inner]) => Some(Type::Arc(Box::new(
                    resolve_annotation_with_self_assoc_and_params(
                        inner,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?,
                ))),
                ("Stream", [inner]) => Some(Type::Stream(Box::new(
                    resolve_annotation_with_self_assoc_and_params(
                        inner,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?,
                ))),
                ("Task", [inner]) => Some(Type::Task(Box::new(
                    resolve_annotation_with_self_assoc_and_params(
                        inner,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?,
                ))),
                ("Tagged", [inner_ann]) => Some(Type::Tagged {
                    inner: Box::new(resolve_annotation_with_self_assoc_and_params(
                        inner_ann,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?),
                    tags: BTreeMap::new(),
                }),
                ("Step", [inner]) => {
                    let inner_ty = resolve_annotation_with_self_assoc_and_params(
                        inner,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )?;
                    Some(Type::Sum(kea_types::SumType {
                        name: "Step".to_string(),
                        type_args: vec![inner_ty.clone()],
                        variants: vec![
                            ("Continue".to_string(), vec![inner_ty.clone()]),
                            ("Halt".to_string(), vec![inner_ty]),
                        ],
                    }))
                }
                _ => resolve_named_type_application(name, args, records, None, |arg_ann| {
                    resolve_annotation_with_self_assoc_and_params(
                        arg_ann,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )
                }),
            }
        }
        TypeAnnotation::Row { fields, rest } => {
            row_annotation_to_type_with(fields, rest, |field_ann| {
                resolve_annotation_with_self_assoc_and_params(
                    field_ann,
                    records,
                    self_type,
                    assoc_types,
                    type_params,
                    placeholder_id,
                )
            })
        }
        TypeAnnotation::EffectRow(_) => None,
        TypeAnnotation::Tuple(elems) => {
            let resolved: Vec<Type> = elems
                .iter()
                .map(|elem| {
                    resolve_annotation_with_self_assoc_and_params(
                        elem,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            Some(Type::Tuple(resolved))
        }
        TypeAnnotation::Forall { type_vars, ty } => {
            let mut scoped_params = type_params.clone();
            let mut local_placeholder = *placeholder_id;
            let mut quantified = Vec::new();
            let mut kinds = BTreeMap::new();
            for name in type_vars {
                let tv = next_placeholder_type_var(&mut local_placeholder);
                scoped_params.insert(name.clone(), Type::Var(tv));
                quantified.push(tv);
                kinds.insert(tv, Kind::Star);
            }
            let resolved = resolve_annotation_with_self_assoc_and_params(
                ty,
                records,
                self_type,
                assoc_types,
                &mut scoped_params,
                &mut local_placeholder,
            )?;
            *placeholder_id = local_placeholder;
            Some(Type::Forall(Box::new(TypeScheme {
                type_vars: quantified,
                row_vars: Vec::new(),
                dim_vars: vec![],
                lacks: BTreeMap::new(),
                bounds: BTreeMap::new(),
                kinds,
                ty: resolved,
            })))
        }
        TypeAnnotation::Function(params, ret) => {
            let resolved_params: Vec<Type> = params
                .iter()
                .map(|param| {
                    resolve_annotation_with_self_assoc_and_params(
                        param,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            let resolved_ret = resolve_annotation_with_self_assoc_and_params(
                ret,
                records,
                self_type,
                assoc_types,
                type_params,
                placeholder_id,
            )?;
            Some(Type::Function(FunctionType {
                params: resolved_params,
                ret: Box::new(resolved_ret),
                effects: EffectRow::pure(),
            }))
        }
        TypeAnnotation::FunctionWithEffect(params, effect, ret) => {
            let resolved_params: Vec<Type> = params
                .iter()
                .map(|param| {
                    resolve_annotation_with_self_assoc_and_params(
                        param,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            let resolved_ret = resolve_annotation_with_self_assoc_and_params(
                ret,
                records,
                self_type,
                assoc_types,
                type_params,
                placeholder_id,
            )?;
            let effects = effect_annotation_to_compat_row(&effect.node, Some(records))
                .unwrap_or_else(pure_effect_row);
            Some(Type::Function(FunctionType {
                params: resolved_params,
                ret: Box::new(resolved_ret),
                effects,
            }))
        }
        TypeAnnotation::Optional(inner) => {
            let resolved = resolve_annotation_with_self_assoc_and_params(
                inner,
                records,
                self_type,
                assoc_types,
                type_params,
                placeholder_id,
            )?;
            Some(Type::Option(Box::new(resolved)))
        }
        TypeAnnotation::Existential {
            bounds,
            associated_types,
        } => {
            let resolved_assoc: Option<BTreeMap<String, Type>> = associated_types
                .iter()
                .map(|(name, ann)| {
                    resolve_annotation_with_self_assoc_and_params(
                        ann,
                        records,
                        self_type,
                        assoc_types,
                        type_params,
                        placeholder_id,
                    )
                    .map(|ty| (name.clone(), ty))
                })
                .collect();
            Some(Type::Existential {
                bounds: bounds.clone(),
                associated_types: resolved_assoc?,
            })
        }
        TypeAnnotation::Projection { .. } | TypeAnnotation::DimLiteral(_) => None,
    }
}

/// Build concrete method types from FnDecl annotations.
///
/// Used for actor protocols which need monomorphic types (not generalized).
/// The generalized types from type_env contain type variables from HM
/// let-generalization (e.g., `forall a r. #{ count: a | r } -> a`), which
/// cause `derive_dispatch_semantics` to see `Var(_)` return types instead
/// of concrete types like `Int` or `Counter`.
///
/// This function reads the type annotations directly from the AST, producing
/// concrete `Function { params: [Self, ...], ret: R }` types suitable for
/// actor protocol dispatch classification. Only the first clause of
/// multi-clause methods is inspected (actor methods should have a single clause).
pub fn concrete_method_types_from_decls(
    type_name: &str,
    methods: &[kea_ast::FnDecl],
    records: &RecordRegistry,
) -> BTreeMap<String, Type> {
    let self_type = records.to_type(type_name).unwrap_or(Type::Dynamic);

    let mut result = BTreeMap::new();
    for method in methods {
        // Build parameter types from annotations
        let mut params = Vec::new();
        for param in &method.params {
            let is_self = param.name() == Some("self");
            if is_self {
                params.push(self_type.clone());
            } else if let Some(ann) = &param.annotation {
                params.push(
                    resolve_annotation_with_self(&ann.node, records, &self_type)
                        .unwrap_or(Type::Dynamic),
                );
            } else {
                // No annotation and not self — fallback to Dynamic
                params.push(Type::Dynamic);
            }
        }

        // Build return type from annotation (Self maps to the concrete type)
        let ret = method
            .return_annotation
            .as_ref()
            .and_then(|ann| resolve_annotation_with_self(&ann.node, records, &self_type))
            .unwrap_or(Type::Unit);

        result.insert(
            method.name.node.clone(),
            Type::Function(FunctionType {
                params,
                ret: Box::new(ret),
                effects: method
                    .effect_annotation
                    .as_ref()
                    .and_then(|ann| effect_annotation_to_compat_row(&ann.node, Some(records)))
                    .unwrap_or_else(pure_effect_row),
            }),
        );
    }
    result
}

/// Extract the concrete type name from a Type, for use in trait satisfaction checks.
/// Returns `Some(name)` for named records; `None` for anonymous records, type vars,
/// and other non-nominal types (where trait checking is deferred or inapplicable).
fn type_name_for_trait_check(ty: &Type) -> Option<String> {
    match ty {
        Type::Record(rt) => Some(rt.name.clone()),
        Type::Sum(st) => Some(st.name.clone()),
        Type::Opaque { name, .. } => Some(name.clone()),
        _ => None,
    }
}

fn instantiate_trait_method_type(
    trait_info: &TraitInfo,
    trait_name: &str,
    method: &TraitMethodInfo,
    unifier: &mut Unifier,
) -> Type {
    let self_var = if let Some(param) = trait_self_param_info(trait_info) {
        unifier.fresh_type_var_with_kind(param.kind.clone())
    } else {
        unifier.fresh_type_var()
    };
    constrain_trait_obligation(
        unifier,
        &Type::Var(self_var),
        trait_name,
        &Provenance {
            span: Span::synthetic(),
            reason: Reason::TraitBound {
                trait_name: trait_name.to_string(),
            },
        },
    );

    let raw_method_ty = Type::Function(FunctionType {
        params: method.param_types.clone(),
        ret: Box::new(method.return_type.clone()),
        effects: method
            .declared_effect
            .as_ref()
            .and_then(|ann| effect_annotation_to_compat_row(ann, None))
            .unwrap_or_else(pure_effect_row),
    });

    let self_placeholder = TypeVarId(u32::MAX);
    let mut type_mapping = BTreeMap::new();
    for tv in free_type_vars(&raw_method_ty) {
        if tv == self_placeholder {
            continue;
        }
        let fresh = if let Some(kind) = method.method_kinds.get(&tv) {
            unifier.fresh_type_var_with_kind(kind.clone())
        } else {
            unifier.fresh_type_var()
        };
        type_mapping.insert(tv, fresh);
    }
    type_mapping.insert(self_placeholder, self_var);
    for (tv, trait_bounds) in &method.method_bounds {
        if let Some(&fresh_tv) = type_mapping.get(tv) {
            for trait_name in trait_bounds {
                constrain_trait_obligation(
                    unifier,
                    &Type::Var(fresh_tv),
                    trait_name,
                    &Provenance {
                        span: Span::synthetic(),
                        reason: Reason::TraitBound {
                            trait_name: trait_name.clone(),
                        },
                    },
                );
            }
        }
    }

    rename_type(
        &raw_method_ty,
        &type_mapping,
        &BTreeMap::new(),
        &BTreeMap::new(),
    )
}

fn span_to_loc(span: Span) -> SourceLocation {
    SourceLocation {
        file_id: span.file.0,
        start: span.start,
        end: span.end,
    }
}

fn annotation_display(ann: &TypeAnnotation) -> String {
    match ann {
        TypeAnnotation::Named(name) => name.clone(),
        TypeAnnotation::Applied(name, args) => {
            let args_str: Vec<String> = args.iter().map(annotation_display).collect();
            format!("{}({})", name, args_str.join(", "))
        }
        TypeAnnotation::Row { fields, rest } => row_annotation_label(fields, rest),
        TypeAnnotation::EffectRow(row) => effect_row_annotation_label(row),
        TypeAnnotation::Tuple(elems) => {
            let elems_str: Vec<String> = elems.iter().map(annotation_display).collect();
            format!("#({})", elems_str.join(", "))
        }
        TypeAnnotation::Forall { type_vars, ty } => {
            format!(
                "forall {}. {}",
                type_vars.join(", "),
                annotation_display(ty)
            )
        }
        TypeAnnotation::Function(params, ret)
        | TypeAnnotation::FunctionWithEffect(params, _, ret) => {
            let params_str: Vec<String> = params.iter().map(annotation_display).collect();
            format!("({}) -> {}", params_str.join(", "), annotation_display(ret))
        }
        TypeAnnotation::Optional(inner) => {
            format!("{}?", annotation_display(inner))
        }
        TypeAnnotation::Existential {
            bounds,
            associated_types,
        } => {
            let bounds_text = if bounds.len() == 1 {
                bounds[0].clone()
            } else {
                format!("({})", bounds.join(", "))
            };
            if associated_types.is_empty() {
                format!("any {bounds_text}")
            } else {
                let assoc_text = associated_types
                    .iter()
                    .map(|(name, ty)| format!("{name} = {}", annotation_display(ty)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("any {bounds_text} where {assoc_text}")
            }
        }
        TypeAnnotation::Projection { base, name } => {
            format!("{base}.{name}")
        }
        TypeAnnotation::DimLiteral(n) => n.to_string(),
    }
}

// ---------------------------------------------------------------------------
// Convenience: resolve the final type
// ---------------------------------------------------------------------------

/// Infer the type of an expression using an [`InferenceContext`].
pub fn infer_expr_in_context(
    expr: &Expr,
    env: &mut TypeEnv,
    ctx: &mut InferenceContext,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Type {
    infer_expr_bidir(expr, env, ctx, records, traits, sum_types)
}

/// Check an expression against an expected type using an [`InferenceContext`].
#[allow(clippy::too_many_arguments)]
pub fn check_expr_in_context(
    expr: &Expr,
    expected: &Type,
    reason: Reason,
    env: &mut TypeEnv,
    ctx: &mut InferenceContext,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Type {
    check_expr_bidir(expr, expected, reason, env, ctx, records, traits, sum_types)
}

/// Infer and resolve the type of an expression using an [`InferenceContext`].
pub fn infer_and_resolve_in_context(
    expr: &Expr,
    env: &mut TypeEnv,
    ctx: &mut InferenceContext,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Type {
    let ty = infer_expr_in_context(expr, env, ctx, records, traits, sum_types);
    ctx.substitution().apply(&ty)
}

/// Infer the type of an expression and return the fully resolved type.
#[cfg(test)]
pub(crate) fn infer_and_resolve(
    expr: &Expr,
    env: &mut TypeEnv,
    unifier: &mut Unifier,
    records: &RecordRegistry,
    traits: &TraitRegistry,
    sum_types: &SumTypeRegistry,
) -> Type {
    let mut ctx = InferenceContext::new();
    std::mem::swap(ctx.unifier_mut(), unifier);
    let resolved = infer_and_resolve_in_context(expr, env, &mut ctx, records, traits, sum_types);
    std::mem::swap(ctx.unifier_mut(), unifier);
    resolved
}
