//! HM type inference with Rémy-style row unification for Kea.
//!
//! This crate implements:
//! - Constraint-based Hindley-Milner type inference
//! - Rémy-style row unification with lacks constraints
//! - Let-generalization preserving row constraints in type schemes
//!
//! The unifier is designed to be extensible: row variables and type variables
//! have separate unification rules, and constraints carry provenance for
//! error reporting (KERNEL §17).

pub mod exhaustive;
pub mod trace;
pub mod typeck;

use kea_ast::Span;
use kea_types::{
    Dim, DimVarId, Kind, Label, LacksConstraints, RowType, RowVarId, Substitution, Type, TypeVarId,
    free_type_vars, type_constructor_for_trait,
};
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicU32, Ordering};

/// Global counters for type/row/dim variable IDs.
///
/// Each `InferenceContext` allocates IDs from these counters so that no two
/// contexts ever produce the same TypeVarId, RowVarId, or DimVarId.  This
/// prevents cross-contamination when `env_free_type_vars` applies one
/// context's substitution to schemes produced by a different context
/// (which happens whenever multiple functions are type-checked against a
/// shared `TypeEnv`, e.g. during module loading or in the REPL).
static GLOBAL_TYPE_VAR: AtomicU32 = AtomicU32::new(0);
static GLOBAL_ROW_VAR: AtomicU32 = AtomicU32::new(0);
static GLOBAL_DIM_VAR: AtomicU32 = AtomicU32::new(0);

/// Allocate a fresh block of variable IDs from the global counters.
///
/// Each context requests `block_size` IDs up-front so that the atomic
/// increment happens once per context rather than once per variable.
const VAR_BLOCK_SIZE: u32 = 1024;

fn alloc_var_block(counter: &AtomicU32) -> u32 {
    counter.fetch_add(VAR_BLOCK_SIZE, Ordering::Relaxed)
}

// Re-export for convenience.
pub use kea_diag::{Category, Diagnostic, DiagnosticError, SourceLocation};
pub use kea_types::TypeScheme;

// ---------------------------------------------------------------------------
// Provenance: why a constraint exists
// ---------------------------------------------------------------------------

/// Tracks the origin of a type constraint for error reporting.
///
/// Every constraint generated during inference carries provenance so that
/// when unification fails, the error message can point to the source
/// location and explain *why* the constraint was generated.
#[derive(Debug, Clone)]
pub struct Provenance {
    pub span: Span,
    pub reason: Reason,
}

/// Why a constraint was generated.
#[derive(Debug, Clone)]
pub enum Reason {
    /// Two sides of a binary operator must be compatible.
    BinaryOp(&'static str),
    /// Function argument must match parameter type.
    FunctionArg { param_index: usize },
    /// Function return value must match declared return type.
    ReturnType,
    /// Let binding: value type matches annotation.
    LetAnnotation,
    /// Expression type must match explicit `as` annotation.
    TypeAscription,
    /// Let binding: usage constrains the bound type.
    LetUsage,
    /// If branches must have the same type.
    IfBranches,
    /// Range literal bounds must have the same type.
    RangeBounds,
    /// Case arms must have the same type.
    CaseArms,
    /// Record field type must match.
    RecordField { label: Label },
    /// Row extension: row must lack this label.
    RowExtension { label: Label },
    /// Pattern must match the scrutinee type.
    PatternMatch,
    /// Trait bound not satisfied.
    TraitBound { trait_name: String },
    /// Actor operation: spawn, send, or call requires Actor type.
    ActorOp,
}

// ---------------------------------------------------------------------------
// Type constraints
// ---------------------------------------------------------------------------

/// A constraint generated during type inference.
#[derive(Debug, Clone)]
pub enum Constraint {
    /// Two types must be equal.
    TypeEqual {
        expected: Type,
        actual: Type,
        provenance: Provenance,
    },
    /// Two row types must be equal.
    RowEqual {
        expected: RowType,
        actual: RowType,
        provenance: Provenance,
    },
    /// A row variable must lack a label (prevents duplicate fields).
    Lacks {
        var: RowVarId,
        label: Label,
        provenance: Provenance,
    },
    /// A type must implement a trait.
    TraitObligation {
        ty: Type,
        trait_name: String,
        provenance: Provenance,
    },
    /// Associated type projection equality obligation.
    AssocTypeEqual {
        base_trait: String,
        base_ty: Type,
        assoc: String,
        rhs: Type,
        provenance: Provenance,
    },
    /// Two kinds must be equal.
    KindEqual {
        expected: Kind,
        actual: Kind,
        provenance: Provenance,
    },
}

/// Constraint storage with lexical scopes.
///
/// Most current call sites emit constraints into a single root scope, but
/// scoped frames are needed for branch-local assumptions (for example GADT
/// refinements) and staged migration to a full constraint IR pipeline.
#[derive(Debug, Clone)]
pub struct ConstraintSet {
    scopes: Vec<Vec<Constraint>>,
}

impl ConstraintSet {
    pub fn new() -> Self {
        Self {
            scopes: vec![Vec::new()],
        }
    }

    /// Push a nested scope. Constraints emitted afterward are local until pop.
    pub fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    /// Pop the current scope.
    ///
    /// When `commit` is true, popped constraints are appended to the parent
    /// scope. When false, they are discarded.
    ///
    /// Returns `false` when attempting to pop the root scope.
    pub fn pop_scope(&mut self, commit: bool) -> bool {
        if self.scopes.len() == 1 {
            return false;
        }
        let popped = self.scopes.pop().expect("checked non-root scope");
        if commit {
            self.scopes
                .last_mut()
                .expect("parent scope exists")
                .extend(popped);
        }
        true
    }

    pub fn push(&mut self, constraint: Constraint) {
        self.scopes
            .last_mut()
            .expect("constraint root scope exists")
            .push(constraint);
    }

    /// Drain all constraints. Any outstanding child scopes are committed to root.
    pub fn drain(&mut self) -> Vec<Constraint> {
        while self.scopes.len() > 1 {
            let popped = self.scopes.pop().expect("checked scope length");
            self.scopes
                .last_mut()
                .expect("root scope exists")
                .extend(popped);
        }
        std::mem::take(
            self.scopes
                .first_mut()
                .expect("constraint root scope exists"),
        )
    }
}

impl Default for ConstraintSet {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Inference context: fresh variable generation and constraint collection
// ---------------------------------------------------------------------------

/// Generates fresh type/row variables and collects constraints during inference.
///
/// Delegates fresh variable generation to the owned `Unifier` so that
/// variable IDs never collide between constraint collection and solving.
pub struct InferenceContext {
    unifier: Unifier,
    constraints: ConstraintSet,
}

impl InferenceContext {
    pub fn new() -> Self {
        Self {
            unifier: Unifier::new(),
            constraints: ConstraintSet::new(),
        }
    }

    /// Create with deterministic variable ID offsets (for tests).
    pub fn with_var_offsets(type_offset: u32, row_offset: u32, dim_offset: u32) -> Self {
        Self {
            unifier: Unifier::with_var_offsets(type_offset, row_offset, dim_offset),
            constraints: ConstraintSet::new(),
        }
    }

    /// Generate a fresh type variable (delegated to the unifier).
    pub fn fresh_type_var(&mut self) -> TypeVarId {
        self.unifier.fresh_type_var()
    }

    /// Generate a fresh type variable as a Type.
    pub fn fresh_type(&mut self) -> Type {
        self.unifier.fresh_type()
    }

    /// Generate a fresh row variable (delegated to the unifier).
    pub fn fresh_row_var(&mut self) -> RowVarId {
        self.unifier.fresh_row_var()
    }

    /// Generate a fresh dimension variable (integer-level inference).
    pub fn fresh_dim_var(&mut self) -> DimVarId {
        self.unifier.fresh_dim_var()
    }

    /// Generate a fresh dimension variable as a `Dim`.
    pub fn fresh_dim(&mut self) -> Dim {
        self.unifier.fresh_dim()
    }

    /// Emit a constraint that two types must be equal.
    pub fn constrain_equal(&mut self, expected: Type, actual: Type, provenance: Provenance) {
        self.constraints.push(Constraint::TypeEqual {
            expected,
            actual,
            provenance,
        });
    }

    /// Emit a constraint that two rows must be equal.
    pub fn constrain_row_equal(
        &mut self,
        expected: RowType,
        actual: RowType,
        provenance: Provenance,
    ) {
        self.constraints.push(Constraint::RowEqual {
            expected,
            actual,
            provenance,
        });
    }

    /// Emit a lacks constraint: row variable must not contain this label.
    pub fn constrain_lacks(&mut self, var: RowVarId, label: Label, provenance: Provenance) {
        self.constraints.push(Constraint::Lacks {
            var,
            label,
            provenance,
        });
    }

    /// Emit a trait obligation.
    pub fn constrain_trait_obligation(
        &mut self,
        ty: Type,
        trait_name: String,
        provenance: Provenance,
    ) {
        self.constraints.push(Constraint::TraitObligation {
            ty,
            trait_name,
            provenance,
        });
    }

    /// Emit an associated-type equality obligation.
    pub fn constrain_assoc_type_equal(
        &mut self,
        base_trait: String,
        base_ty: Type,
        assoc: String,
        rhs: Type,
        provenance: Provenance,
    ) {
        self.constraints.push(Constraint::AssocTypeEqual {
            base_trait,
            base_ty,
            assoc,
            rhs,
            provenance,
        });
    }

    /// Emit a kind equality obligation.
    pub fn constrain_kind_equal(&mut self, expected: Kind, actual: Kind, provenance: Provenance) {
        self.constraints.push(Constraint::KindEqual {
            expected,
            actual,
            provenance,
        });
    }

    /// Start a nested constraint scope.
    pub fn push_constraint_scope(&mut self) {
        self.constraints.push_scope();
    }

    /// Pop the current constraint scope.
    ///
    /// See [`ConstraintSet::pop_scope`] for `commit` semantics.
    pub fn pop_constraint_scope(&mut self, commit: bool) -> bool {
        self.constraints.pop_scope(commit)
    }

    /// Solve the collected constraints using the owned unifier.
    pub fn solve(&mut self) -> Result<(), DiagnosticError> {
        let constraints = self.constraints.drain();
        self.unifier.solve(constraints)
    }

    /// Mutably access the underlying unifier.
    ///
    /// This is crate-scoped on purpose: mutation should stay inside
    /// type-inference internals so downstream crates use context APIs.
    #[cfg(test)]
    pub(crate) fn unifier_mut(&mut self) -> &mut Unifier {
        &mut self.unifier
    }

    /// Read-only access to the current substitution.
    pub fn substitution(&self) -> &Substitution {
        &self.unifier.substitution
    }

    /// Retrieve accumulated errors without consuming the context.
    pub fn errors(&self) -> &[Diagnostic] {
        self.unifier.errors()
    }

    /// Check if solving/inference has produced any errors.
    pub fn has_errors(&self) -> bool {
        self.unifier.has_errors()
    }

    /// Enable step-by-step unification tracing for observability tools.
    pub fn enable_tracing(&mut self) {
        self.unifier.enable_tracing();
    }

    /// Enable capture of emitted constraints for observability tools.
    pub fn enable_constraint_capture(&mut self) {
        self.unifier.enable_constraint_capture();
    }

    /// Disable capture and clear any buffered constraints.
    pub fn disable_constraint_capture(&mut self) {
        self.unifier.disable_constraint_capture();
    }

    /// Take and clear captured constraints.
    pub fn take_captured_constraints(&mut self) -> Vec<Constraint> {
        self.unifier.take_captured_constraints()
    }

    /// Whether unification tracing is currently enabled.
    pub fn is_tracing(&self) -> bool {
        self.unifier.is_tracing()
    }

    /// Get the collected unification trace.
    pub fn unify_trace(&self) -> &[crate::trace::UnifyStep] {
        self.unifier.unify_trace()
    }

    /// Check accumulated trait bounds against the trait registry.
    pub fn check_trait_bounds(&mut self, trait_registry: &crate::typeck::TraitRegistry) {
        self.unifier.check_trait_bounds(trait_registry);
    }

    /// Extract and clear collected runtime type annotations.
    pub fn take_type_annotations(&mut self) -> crate::typeck::TypeAnnotations {
        self.unifier.take_type_annotations()
    }
}

impl Default for InferenceContext {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for InferenceContext {
    type Target = Unifier;

    fn deref(&self) -> &Self::Target {
        &self.unifier
    }
}

impl DerefMut for InferenceContext {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.unifier
    }
}

fn canonicalize_type_scheme_for_alpha_eq(scheme: &TypeScheme) -> TypeScheme {
    let mut subst = Substitution::new();
    let mut canonical_type_vars = Vec::with_capacity(scheme.type_vars.len());
    let mut canonical_row_vars = Vec::with_capacity(scheme.row_vars.len());
    let mut canonical_dim_vars = Vec::with_capacity(scheme.dim_vars.len());
    let mut type_var_map = std::collections::BTreeMap::new();
    let mut row_var_map = std::collections::BTreeMap::new();

    for (idx, tv) in scheme.type_vars.iter().enumerate() {
        let canonical = TypeVarId(idx as u32);
        canonical_type_vars.push(canonical);
        type_var_map.insert(*tv, canonical);
        if *tv != canonical {
            subst.bind_type(*tv, Type::Var(canonical));
        }
    }
    for (idx, rv) in scheme.row_vars.iter().enumerate() {
        let canonical = RowVarId(idx as u32);
        canonical_row_vars.push(canonical);
        row_var_map.insert(*rv, canonical);
        if *rv != canonical {
            subst.bind_row(
                *rv,
                RowType {
                    fields: vec![],
                    rest: Some(canonical),
                },
            );
        }
    }
    for (idx, dv) in scheme.dim_vars.iter().enumerate() {
        let canonical = DimVarId(idx as u32);
        canonical_dim_vars.push(canonical);
        if *dv != canonical {
            subst.bind_dim(*dv, Dim::Var(canonical));
        }
    }

    let ty = subst.apply(&scheme.ty);
    let lacks = scheme
        .lacks
        .iter()
        .map(|(rv, labels)| {
            (
                *row_var_map.get(rv).unwrap_or(rv),
                labels.iter().cloned().collect(),
            )
        })
        .collect();
    let bounds = scheme
        .bounds
        .iter()
        .map(|(tv, trait_bounds)| {
            (
                *type_var_map.get(tv).unwrap_or(tv),
                trait_bounds.iter().cloned().collect(),
            )
        })
        .collect();
    let kinds = scheme
        .kinds
        .iter()
        .map(|(tv, kind)| (*type_var_map.get(tv).unwrap_or(tv), kind.clone()))
        .collect();

    TypeScheme {
        type_vars: canonical_type_vars,
        row_vars: canonical_row_vars,
        dim_vars: canonical_dim_vars,
        lacks,
        bounds,
        kinds,
        ty,
    }
}

fn alpha_equivalent_type_schemes(left: &TypeScheme, right: &TypeScheme) -> bool {
    canonicalize_type_scheme_for_alpha_eq(left) == canonicalize_type_scheme_for_alpha_eq(right)
}

// ---------------------------------------------------------------------------
// Unifier: solves constraints
// ---------------------------------------------------------------------------

/// Solves type constraints via unification.
///
/// Handles both standard type unification and Rémy-style row unification.
/// Maintains a substitution and lacks constraints that grow during solving.
/// Also generates fresh type/row variables for use during inference.
#[derive(Clone)]
pub struct Unifier {
    pub substitution: Substitution,
    pub lacks: LacksConstraints,
    /// Trait bounds accumulated during instantiation. Maps type vars to their
    /// required trait names. Checked after inference resolves concrete types.
    pub trait_bounds: std::collections::BTreeMap<TypeVarId, std::collections::BTreeSet<String>>,
    /// Best-effort source spans for trait bounds tracked in `trait_bounds`.
    trait_bound_spans: std::collections::BTreeMap<(TypeVarId, String), Span>,
    /// Non-variable trait obligations deferred until concrete solving.
    pending_trait_obligations: Vec<PendingTraitObligation>,
    /// Projection equalities deferred until trait solving.
    pending_assoc_equalities: Vec<PendingAssocTypeEquality>,
    /// Kind assignments for type variables introduced with explicit kinds.
    pub type_var_kinds: std::collections::BTreeMap<TypeVarId, Kind>,
    /// Named type parameters available while resolving annotations in the
    /// current function declaration (for example `F` in `F(a)`).
    pub annotation_type_param_scope: std::collections::BTreeMap<String, Type>,
    /// Runtime-oriented type annotations emitted from inference.
    pub type_annotations: crate::typeck::TypeAnnotations,
    /// Pending call-site evidence requirements: call span -> type vars seen at that site.
    pending_evidence_sites: std::collections::BTreeMap<Span, std::collections::BTreeSet<TypeVarId>>,
    /// Current nested lambda depth while inferring an expression.
    lambda_depth: usize,
    /// Bidirectional expected type hint for constructor disambiguation.
    /// Set by `check_expr_bidir` before calling `infer_expr_bidir`,
    /// consumed by constructor resolution sites.
    bidir_expected_type: Option<Type>,
    errors: Vec<Diagnostic>,
    next_type_var: u32,
    next_row_var: u32,
    next_dim_var: u32,
    /// When true, unification steps are recorded for observability tools.
    tracing: bool,
    /// Unification trace steps (populated only when `tracing` is true).
    unify_trace: Vec<crate::trace::UnifyStep>,
    /// When true, every incoming constraint is captured before execution.
    capture_constraints: bool,
    /// Captured constraints for observability tools.
    captured_constraints: Vec<Constraint>,
}

#[derive(Debug, Clone, Copy)]
struct SolveOptions {
    max_iterations: usize,
    trace_limit: usize,
}

impl Default for SolveOptions {
    fn default() -> Self {
        Self {
            // High default guard to avoid behavior changes while still preventing
            // accidental non-termination as new constraint kinds are introduced.
            max_iterations: 1_000_000,
            trace_limit: 8,
        }
    }
}

enum TraitImplStatus {
    Unique(crate::typeck::SolvedCandidate),
    Ambiguous,
    NoMatch,
}

#[derive(Debug, Clone)]
struct PendingTraitObligation {
    ty: Type,
    trait_name: String,
    provenance: Provenance,
}

#[derive(Debug, Clone)]
struct PendingAssocTypeEquality {
    base_trait: String,
    base_ty: Type,
    assoc: String,
    rhs: Type,
    provenance: Provenance,
}

#[derive(Clone)]
pub(crate) struct UnifierScope {
    snapshot: Box<Unifier>,
    error_len: usize,
}

impl Unifier {
    fn trait_impl_status(
        trait_registry: &crate::typeck::TraitRegistry,
        trait_name: &str,
        ty: &Type,
    ) -> TraitImplStatus {
        match trait_registry.solve_goal(&crate::typeck::TraitGoal::Implements {
            trait_name: trait_name.to_string(),
            ty: ty.clone(),
        }) {
            crate::typeck::SolveOutcome::Unique(candidate) => TraitImplStatus::Unique(candidate),
            crate::typeck::SolveOutcome::Ambiguous(_) => TraitImplStatus::Ambiguous,
            crate::typeck::SolveOutcome::NoMatch(_) => TraitImplStatus::NoMatch,
        }
    }

    fn trait_nomatch_detail(reasons: &[crate::typeck::MismatchReason]) -> Option<String> {
        reasons.iter().find_map(|reason| match reason {
            crate::typeck::MismatchReason::FundepConflict { dependency } => Some(format!(
                "functional dependency conflict while solving `{dependency}`"
            )),
            crate::typeck::MismatchReason::NoImplForConstructor {
                trait_name,
                type_constructor,
            } => Some(format!(
                "no `{trait_name}` impl found for type constructor `{type_constructor}`"
            )),
            crate::typeck::MismatchReason::ParamBoundUnsatisfied {
                param,
                bound_trait,
                ty,
            } => Some(format!(
                "bound `{param}: {bound_trait}` is unsatisfied for `{ty}`"
            )),
            crate::typeck::MismatchReason::SupertraitUnsatisfied { supertrait, ty } => Some(
                format!("required supertrait `{supertrait}` is unsatisfied for `{ty}`"),
            ),
            _ => None,
        })
    }

    pub fn new() -> Self {
        Self::with_var_offsets(
            alloc_var_block(&GLOBAL_TYPE_VAR),
            alloc_var_block(&GLOBAL_ROW_VAR),
            alloc_var_block(&GLOBAL_DIM_VAR),
        )
    }

    /// Create a context with explicit starting offsets for variable IDs.
    ///
    /// Production code should use `new()` (which allocates from a global
    /// counter).  This constructor exists for unit tests that need
    /// deterministic TypeVarIds starting at 0.
    pub fn with_var_offsets(next_type_var: u32, next_row_var: u32, next_dim_var: u32) -> Self {
        Self {
            substitution: Substitution::new(),
            lacks: LacksConstraints::new(),
            trait_bounds: std::collections::BTreeMap::new(),
            trait_bound_spans: std::collections::BTreeMap::new(),
            pending_trait_obligations: Vec::new(),
            pending_assoc_equalities: Vec::new(),
            type_var_kinds: std::collections::BTreeMap::new(),
            annotation_type_param_scope: std::collections::BTreeMap::new(),
            type_annotations: crate::typeck::TypeAnnotations::default(),
            pending_evidence_sites: std::collections::BTreeMap::new(),
            lambda_depth: 0,
            bidir_expected_type: None,
            errors: Vec::new(),
            next_type_var,
            next_row_var,
            next_dim_var,
            tracing: false,
            unify_trace: Vec::new(),
            capture_constraints: false,
            captured_constraints: Vec::new(),
        }
    }

    /// Generate a fresh type variable.
    pub fn fresh_type_var(&mut self) -> TypeVarId {
        let id = TypeVarId(self.next_type_var);
        self.next_type_var += 1;
        id
    }

    /// Generate a fresh type variable with an explicit kind assignment.
    pub fn fresh_type_var_with_kind(&mut self, kind: Kind) -> TypeVarId {
        let id = self.fresh_type_var();
        self.type_var_kinds.insert(id, kind);
        id
    }

    /// Replace the active annotation type-parameter scope.
    pub fn set_annotation_type_param_scope(
        &mut self,
        scope: std::collections::BTreeMap<String, Type>,
    ) {
        self.annotation_type_param_scope = scope;
    }

    /// Look up a named annotation type parameter by name.
    pub fn annotation_type_param(&self, name: &str) -> Option<&Type> {
        self.annotation_type_param_scope.get(name)
    }

    /// Get or insert a kind-* annotation type parameter.
    pub fn annotation_type_param_or_insert_star(&mut self, name: &str) -> Type {
        if let Some(existing) = self.annotation_type_param_scope.get(name) {
            return existing.clone();
        }
        let tv = self.fresh_type_var_with_kind(Kind::Star);
        let ty = Type::Var(tv);
        self.annotation_type_param_scope
            .insert(name.to_string(), ty.clone());
        ty
    }

    /// Generate a fresh type variable as a Type.
    pub fn fresh_type(&mut self) -> Type {
        Type::Var(self.fresh_type_var())
    }

    /// Keep fresh-variable counters monotone relative to another solver.
    ///
    /// Useful when type-checking speculative/branch-local paths with a cloned
    /// unifier and then continuing inference on the original unifier.
    pub fn absorb_fresh_counters(&mut self, other: &Unifier) {
        self.next_type_var = self.next_type_var.max(other.next_type_var);
        self.next_row_var = self.next_row_var.max(other.next_row_var);
        self.next_dim_var = self.next_dim_var.max(other.next_dim_var);
    }

    /// Begin a branch-local scope for speculative inference.
    ///
    /// Scopes are used by bidirectional checking paths (for example `case`
    /// arms) that must keep diagnostics while rolling back branch-local
    /// substitutions and deferred obligations.
    pub(crate) fn begin_scope(&self) -> UnifierScope {
        UnifierScope {
            snapshot: Box::new(self.clone()),
            error_len: self.errors.len(),
        }
    }

    /// End a branch-local scope.
    ///
    /// When `commit` is false, branch-local solver state is discarded while
    /// preserving any diagnostics emitted inside the scope and keeping fresh
    /// counters monotone.
    pub(crate) fn end_scope(&mut self, scope: UnifierScope, commit: bool) {
        if commit {
            return;
        }

        let next_type_var = self.next_type_var;
        let next_row_var = self.next_row_var;
        let next_dim_var = self.next_dim_var;
        let new_errors = if scope.error_len < self.errors.len() {
            self.errors[scope.error_len..].to_vec()
        } else {
            Vec::new()
        };
        // Preserve type annotations (spawn_kinds, evidence_sites, use_desugared,
        // for_desugared, resolved_variants, etc.) across scope rollback. These
        // are semantic decisions that the evaluator needs regardless of whether
        // the unification scope commits or rolls back.
        let annotations = std::mem::take(&mut self.type_annotations);

        *self = *scope.snapshot;
        self.next_type_var = self.next_type_var.max(next_type_var);
        self.next_row_var = self.next_row_var.max(next_row_var);
        self.next_dim_var = self.next_dim_var.max(next_dim_var);
        self.errors.extend(new_errors);
        // Merge annotations from the rolled-back scope into the restored state.
        for (span, sites) in annotations.evidence_sites {
            self.type_annotations.evidence_sites.insert(span, sites);
        }
        for (span, packs) in annotations.existential_packs {
            self.type_annotations.existential_packs.insert(span, packs);
        }
        for (span, lowered) in annotations.for_desugared {
            self.type_annotations.for_desugared.insert(span, lowered);
        }
        for (span, lowered) in annotations.use_desugared {
            self.type_annotations.use_desugared.insert(span, lowered);
        }
        for (span, kind) in annotations.spawn_kinds {
            self.type_annotations.spawn_kinds.insert(span, kind);
        }
        for (span, type_name) in annotations.resolved_variants {
            self.type_annotations
                .resolved_variants
                .insert(span, type_name);
        }
        for (span, target) in annotations.expect_type_targets {
            self.type_annotations
                .expect_type_targets
                .insert(span, target);
        }
    }

    /// Generate a fresh row variable.
    pub fn fresh_row_var(&mut self) -> RowVarId {
        let id = RowVarId(self.next_row_var);
        self.next_row_var += 1;
        id
    }

    /// Generate a fresh dimension variable.
    pub fn fresh_dim_var(&mut self) -> DimVarId {
        let id = DimVarId(self.next_dim_var);
        self.next_dim_var += 1;
        id
    }

    /// Generate a fresh dimension variable as a `Dim`.
    pub fn fresh_dim(&mut self) -> Dim {
        Dim::Var(self.fresh_dim_var())
    }

    /// Resolve a dimension through substitution.
    pub fn resolve_dim(&self, dim: &Dim) -> Dim {
        self.substitution.apply_dim(dim)
    }

    /// Unify two dimensions.
    pub fn unify_dim(&mut self, expected: &Dim, actual: &Dim, provenance: &Provenance) {
        let expected = self.resolve_dim(expected);
        let actual = self.resolve_dim(actual);
        match (&expected, &actual) {
            (Dim::Known(left), Dim::Known(right)) if left != right => {
                self.errors.push(
                    Diagnostic::error(
                        Category::TypeMismatch,
                        format!("dimension mismatch: expected `{left}`, got `{right}`"),
                    )
                    .at(span_to_location(provenance.span)),
                );
            }
            (Dim::Var(var), dim) | (dim, Dim::Var(var)) => {
                if matches!(dim, Dim::Var(other) if other == var) {
                    return;
                }
                self.substitution.bind_dim(*var, dim.clone());
            }
            _ => {}
        }
    }

    /// Apply a single constraint through the centralized constraint executor.
    pub fn constrain(&mut self, constraint: Constraint) {
        if self.capture_constraints {
            self.captured_constraints.push(constraint.clone());
        }
        self.apply_constraint(constraint);
    }

    /// Enable capture of incoming constraints.
    pub fn enable_constraint_capture(&mut self) {
        self.capture_constraints = true;
        self.captured_constraints.clear();
    }

    /// Disable capture and clear buffered constraints.
    pub fn disable_constraint_capture(&mut self) {
        self.capture_constraints = false;
        self.captured_constraints.clear();
    }

    /// Take and clear the captured constraint log.
    pub fn take_captured_constraints(&mut self) -> Vec<Constraint> {
        std::mem::take(&mut self.captured_constraints)
    }

    /// Unify two types by emitting a type-equality constraint.
    ///
    /// Constraint solving remains deterministic; diagnostics are still
    /// accumulated on the unifier.
    ///
    /// Test-only convenience shim. Production inference code should emit
    /// constraints through `constrain(...)` (or typeck helpers) instead.
    #[cfg(test)]
    pub fn unify(&mut self, expected: &Type, actual: &Type, provenance: &Provenance) {
        self.constrain(Constraint::TypeEqual {
            expected: expected.clone(),
            actual: actual.clone(),
            provenance: provenance.clone(),
        });
    }

    fn unify_immediate(&mut self, expected: &Type, actual: &Type, provenance: &Provenance) {
        let expected = self.substitution.apply(expected);
        let actual = self.substitution.apply(actual);

        match (&expected, &actual) {
            // Identical types: nothing to do.
            _ if expected == actual => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Identity,
                    &expected,
                    &actual,
                    "types already equal".into(),
                );
            }

            // Type variable on either side: bind it.
            (Type::Var(v), _) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Bind,
                    &expected,
                    &actual,
                    format!("t{} := {}", v.0, kea_types::sanitize_type_display(&actual)),
                );
                self.bind_type_var(*v, &actual, provenance);
            }
            (_, Type::Var(v)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Bind,
                    &expected,
                    &actual,
                    format!(
                        "t{} := {}",
                        v.0,
                        kea_types::sanitize_type_display(&expected)
                    ),
                );
                self.bind_type_var(*v, &expected, provenance);
            }

            // Bottom type unifies with any type.
            (Type::Never, _) | (_, Type::Never) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Identity,
                    &expected,
                    &actual,
                    "Never is bottom and unifies with any type".into(),
                );
            }

            // Dynamic widening: concrete → Dynamic is always safe (losing type info).
            (Type::Dynamic, _) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Identity,
                    &expected,
                    &actual,
                    "concrete type widens to Dynamic".into(),
                );
            }
            // Dynamic narrowing: Dynamic → concrete requires explicit assertion.
            (_, Type::Dynamic) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Error,
                    &expected,
                    &actual,
                    "Dynamic does not implicitly narrow to concrete type".into(),
                );
                let expected_display = kea_types::sanitize_type_display(&expected);
                let mut diag = Diagnostic::error(
                    Category::TypeMismatch,
                    format!("cannot use `Dynamic` value as `{expected_display}`"),
                )
                .at(span_to_location(provenance.span));
                diag = diag.with_help(
                    "use `expect_type` to assert the runtime type, \
                     e.g. `let x: Int = expect_type(val)?`",
                );
                self.errors.push(diag);
            }

            // Constructor application terms.
            (Type::App(f1, args1), Type::App(f2, args2)) if args1.len() == args2.len() => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "App(F, args) ~ App(G, args) → unify constructors and args".into(),
                );
                self.unify_immediate(f1, f2, provenance);
                for (a, b) in args1.iter().zip(args2.iter()) {
                    self.unify_immediate(a, b, provenance);
                }
            }
            (Type::App(f, app_args), concrete) if matches!(f.as_ref(), Type::Var(_)) => {
                let Type::Var(constructor_var) = f.as_ref() else {
                    unreachable!("guard guarantees constructor var");
                };
                if !self.unify_constructor_application_var(
                    *constructor_var,
                    app_args,
                    concrete,
                    provenance,
                ) {
                    self.push_unify_step(
                        crate::trace::UnifyAction::Error,
                        &expected,
                        &actual,
                        "type mismatch".into(),
                    );
                    let (message, help) =
                        type_mismatch_message(&expected, &actual, &provenance.reason);
                    let mut diag = Diagnostic::error(Category::TypeMismatch, message)
                        .at(span_to_location(provenance.span));
                    if let Some(help_text) = help {
                        diag = diag.with_help(help_text);
                    }
                    self.errors.push(diag);
                }
            }
            (concrete, Type::App(f, app_args)) if matches!(f.as_ref(), Type::Var(_)) => {
                let Type::Var(constructor_var) = f.as_ref() else {
                    unreachable!("guard guarantees constructor var");
                };
                if !self.unify_constructor_application_var(
                    *constructor_var,
                    app_args,
                    concrete,
                    provenance,
                ) {
                    self.push_unify_step(
                        crate::trace::UnifyAction::Error,
                        &expected,
                        &actual,
                        "type mismatch".into(),
                    );
                    let (message, help) =
                        type_mismatch_message(&expected, &actual, &provenance.reason);
                    let mut diag = Diagnostic::error(Category::TypeMismatch, message)
                        .at(span_to_location(provenance.span));
                    if let Some(help_text) = help {
                        diag = diag.with_help(help_text);
                    }
                    self.errors.push(diag);
                }
            }

            // Structural recursion for compound types.
            (
                Type::Decimal {
                    precision: left_precision,
                    scale: left_scale,
                },
                Type::Decimal {
                    precision: right_precision,
                    scale: right_scale,
                },
            ) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Decimal(P1,S1) ~ Decimal(P2,S2) → unify dimensions".into(),
                );
                self.unify_dim(left_precision, right_precision, provenance);
                self.unify_dim(left_scale, right_scale, provenance);
            }
            (
                Type::FixedSizeList {
                    element: left_element,
                    size: left_size,
                },
                Type::FixedSizeList {
                    element: right_element,
                    size: right_size,
                },
            ) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "FixedSizeList(A,N) ~ FixedSizeList(B,M) → unify A~B and N~M".into(),
                );
                self.unify_immediate(left_element, right_element, provenance);
                self.unify_dim(left_size, right_size, provenance);
            }
            (
                Type::Tensor {
                    element: left_element,
                    shape: left_shape,
                },
                Type::Tensor {
                    element: right_element,
                    shape: right_shape,
                },
            ) => {
                if left_shape.len() != right_shape.len() {
                    self.push_unify_step(
                        crate::trace::UnifyAction::Error,
                        &expected,
                        &actual,
                        format!(
                            "Tensor rank mismatch: expected rank {}, got rank {}",
                            left_shape.len(),
                            right_shape.len()
                        ),
                    );
                    self.errors.push(
                        Diagnostic::error(
                            Category::TypeMismatch,
                            format!(
                                "tensor rank mismatch: expected rank {}, got rank {}",
                                left_shape.len(),
                                right_shape.len()
                            ),
                        )
                        .at(span_to_location(provenance.span)),
                    );
                    return;
                }
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Tensor(A,S1) ~ Tensor(B,S2) → unify A~B and each dimension".into(),
                );
                self.unify_immediate(left_element, right_element, provenance);
                for (left_dim, right_dim) in left_shape.iter().zip(right_shape.iter()) {
                    self.unify_dim(left_dim, right_dim, provenance);
                }
            }
            (Type::List(a), Type::List(b)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "List(A) ~ List(B) → unify A ~ B".into(),
                );
                self.unify_immediate(a, b, provenance);
            }
            (Type::Set(a), Type::Set(b)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Set(A) ~ Set(B) → unify A ~ B".into(),
                );
                self.unify_immediate(a, b, provenance);
            }
            (Type::Option(a), Type::Option(b)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Option(A) ~ Option(B) → unify A ~ B".into(),
                );
                self.unify_immediate(a, b, provenance);
            }
            (Type::Map(k1, v1), Type::Map(k2, v2)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Map(K1,V1) ~ Map(K2,V2) → unify K1~K2, V1~V2".into(),
                );
                self.unify_immediate(k1, k2, provenance);
                self.unify_immediate(v1, v2, provenance);
            }
            (Type::Result(ok1, err1), Type::Result(ok2, err2)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Result(A,E1) ~ Result(B,E2) → unify A~B, E1~E2".into(),
                );
                self.unify_immediate(ok1, ok2, provenance);
                self.unify_immediate(err1, err2, provenance);
            }
            (
                Type::Existential {
                    bounds: bounds_a,
                    associated_types: assoc_a,
                },
                Type::Existential {
                    bounds: bounds_b,
                    associated_types: assoc_b,
                },
            ) if bounds_a == bounds_b && assoc_a.len() == assoc_b.len() => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Existential ~ Existential → unify associated type constraints".into(),
                );
                for (name, ty_a) in assoc_a {
                    let Some(ty_b) = assoc_b.get(name) else {
                        self.push_unify_step(
                            crate::trace::UnifyAction::Error,
                            &expected,
                            &actual,
                            format!("existential associated type `{name}` missing on right side"),
                        );
                        self.errors.push(
                            Diagnostic::error(
                                Category::TypeMismatch,
                                "existential associated type constraints do not match".to_string(),
                            )
                            .at(span_to_location(provenance.span)),
                        );
                        return;
                    };
                    self.unify_immediate(ty_a, ty_b, provenance);
                }
            }
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    format!("Tuple({}) ~ Tuple({}) → unify pairwise", a.len(), b.len()),
                );
                for (a, b) in a.iter().zip(b.iter()) {
                    self.unify_immediate(a, b, provenance);
                }
            }
            (Type::Function(a), Type::Function(b)) if a.params.len() == b.params.len() => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Function ~ Function → unify params + effects + return".into(),
                );
                for (a, b) in a.params.iter().zip(b.params.iter()) {
                    self.unify_immediate(a, b, provenance);
                }
                self.unify_rows_immediate(&a.effects.row, &b.effects.row, provenance);
                self.unify_immediate(&a.ret, &b.ret, provenance);
            }
            (Type::Forall(a), Type::Forall(b)) if alpha_equivalent_type_schemes(a, b) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Forall ~ Forall → alpha-equal quantified schemes".into(),
                );
            }
            (Type::Stream(a), Type::Stream(b)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Stream(A) ~ Stream(B) → unify A ~ B".into(),
                );
                self.unify_immediate(a, b, provenance);
            }
            (Type::Task(a), Type::Task(b)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Task(A) ~ Task(B) → unify A ~ B".into(),
                );
                self.unify_immediate(a, b, provenance);
            }
            (Type::Tagged { inner: a, tags: t1 }, Type::Tagged { inner: b, tags: t2 }) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Tagged ~ Tagged → unify inner".into(),
                );
                self.unify_immediate(a, b, provenance);
                if t1 != t2 {
                    self.errors.push(
                        Diagnostic::error(
                            Category::TypeMismatch,
                            format!("incompatible dimensional tags: {t1:?} vs {t2:?}"),
                        )
                        .at(span_to_location(provenance.span)),
                    );
                }
            }
            (Type::Actor(a), Type::Actor(b)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Actor(A) ~ Actor(B) → unify A ~ B".into(),
                );
                self.unify_immediate(a, b, provenance);
            }
            (Type::Arc(a), Type::Arc(b)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    "Arc(A) ~ Arc(B) → unify A ~ B".into(),
                );
                self.unify_immediate(a, b, provenance);
            }

            // Row unification.
            (Type::Row(a), Type::Row(b)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::UnifyRows,
                    &expected,
                    &actual,
                    "Row ~ Row → row unification".into(),
                );
                self.unify_rows_immediate(a, b, provenance);
            }
            (Type::AnonRecord(a), Type::AnonRecord(b)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::UnifyRows,
                    &expected,
                    &actual,
                    "AnonRecord ~ AnonRecord → row unification".into(),
                );
                self.unify_rows_immediate(a, b, provenance);
            }

            // Named record: must be same name, then unify rows.
            (Type::Record(a), Type::Record(b)) if a.name == b.name => {
                self.push_unify_step(
                    crate::trace::UnifyAction::UnifyRows,
                    &expected,
                    &actual,
                    format!("Record({}) ~ Record({}) → row unification", a.name, b.name),
                );
                self.unify_rows_immediate(&a.row, &b.row, provenance);
            }

            // Structural projection: named record unifies with anonymous row.
            // A function expecting `{name: String | r}` accepts `User` — the named
            // record's fields are expanded and unified structurally, with the row
            // variable absorbing extras.
            //
            // Decision 10: named records are nominal, anonymous records are structural.
            // Structural projection (named → structural) is allowed at the unifier
            // level for both open and closed anonymous records, because inference
            // creates closed anonymous records as intermediates (e.g. field access
            // on a type variable creates an open row that gets fully resolved).
            //
            // The surface-level check (blocking `#{ ... }` where `Patent` is expected)
            // is enforced at expression inference, not here.
            (Type::AnonRecord(row), Type::Record(rec))
            | (Type::Record(rec), Type::AnonRecord(row)) => {
                self.push_unify_step(
                    crate::trace::UnifyAction::UnifyRows,
                    &expected,
                    &actual,
                    format!(
                        "structural projection: Record({}) ~ AnonRecord → row unification",
                        rec.name
                    ),
                );
                self.unify_rows_immediate(row, &rec.row, provenance);
            }

            // Sum types: same name, unify variant fields pairwise.
            (Type::Sum(a), Type::Sum(b))
                if a.name == b.name
                    && a.type_args.len() == b.type_args.len()
                    && a.variants.len() == b.variants.len() =>
            {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    format!("Sum({}) ~ Sum({}) → unify variants", a.name, b.name),
                );
                for (a_arg, b_arg) in a.type_args.iter().zip(b.type_args.iter()) {
                    self.unify_immediate(a_arg, b_arg, provenance);
                }
                for ((_, a_fields), (_, b_fields)) in a.variants.iter().zip(b.variants.iter()) {
                    for (af, bf) in a_fields.iter().zip(b_fields.iter()) {
                        self.unify_immediate(af, bf, provenance);
                    }
                }
            }

            // Recursive placeholder support: during recursive sum registration we
            // may carry shallow references (`variants = []`) in field positions.
            // Treat these as nominal references that match by type name.
            (Type::Sum(a), Type::Sum(b))
                if a.name == b.name && (a.variants.is_empty() || b.variants.is_empty()) =>
            {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    format!(
                        "Sum({}) placeholder ~ Sum({}) → nominal match",
                        a.name, b.name
                    ),
                );
                if a.type_args.len() == b.type_args.len() {
                    for (a_arg, b_arg) in a.type_args.iter().zip(b.type_args.iter()) {
                        self.unify_immediate(a_arg, b_arg, provenance);
                    }
                }
            }

            // Opaque types: nominal, unify only by same name + params.
            (
                Type::Opaque {
                    name: expected_name,
                    params: expected_params,
                },
                Type::Opaque {
                    name: actual_name,
                    params: actual_params,
                },
            ) if expected_name == actual_name && expected_params.len() == actual_params.len() => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Decompose,
                    &expected,
                    &actual,
                    format!("Opaque({expected_name}) ~ Opaque({actual_name}) → unify parameters"),
                );
                for (lhs, rhs) in expected_params.iter().zip(actual_params.iter()) {
                    self.unify_immediate(lhs, rhs, provenance);
                }
            }

            // Everything else is a type mismatch.
            _ => {
                self.push_unify_step(
                    crate::trace::UnifyAction::Error,
                    &expected,
                    &actual,
                    "type mismatch".into(),
                );
                let (message, help) = type_mismatch_message(&expected, &actual, &provenance.reason);
                let mut diag = Diagnostic::error(Category::TypeMismatch, message)
                    .at(span_to_location(provenance.span));
                if let Some(help_text) = help {
                    diag = diag.with_help(help_text);
                }
                self.errors.push(diag);
            }
        }
    }

    fn unify_constructor_application_var(
        &mut self,
        constructor_var: TypeVarId,
        app_args: &[Type],
        concrete: &Type,
        provenance: &Provenance,
    ) -> bool {
        let Some((constructor_name, concrete_args)) = type_constructor_for_trait(concrete) else {
            return false;
        };

        if app_args.len() > concrete_args.len() {
            return false;
        }

        self.push_unify_step(
            crate::trace::UnifyAction::RemyDecompose,
            &Type::App(Box::new(Type::Var(constructor_var)), app_args.to_vec()),
            concrete,
            format!(
                "constructor application: bind F to {} with {} fixed args",
                constructor_name,
                concrete_args.len().saturating_sub(app_args.len())
            ),
        );

        for (app_arg, concrete_arg) in app_args.iter().zip(concrete_args.iter()) {
            self.unify_immediate(app_arg, concrete_arg, provenance);
        }

        let fixed_args = concrete_args
            .iter()
            .enumerate()
            .skip(app_args.len())
            .map(|(idx, ty)| (idx, ty.clone()))
            .collect();

        let constructor = Type::Constructor {
            name: constructor_name,
            fixed_args,
            arity: concrete_args.len(),
        };
        self.bind_type_var(constructor_var, &constructor, provenance);
        true
    }

    /// Rémy-style row unification (KERNEL §2.2) via row-equality constraints.
    ///
    /// Test-only convenience shim. Production inference code should emit
    /// row-equality constraints through `constrain(...)`.
    #[cfg(test)]
    pub fn unify_rows(&mut self, expected: &RowType, actual: &RowType, provenance: &Provenance) {
        self.constrain(Constraint::RowEqual {
            expected: expected.clone(),
            actual: actual.clone(),
            provenance: provenance.clone(),
        });
    }

    /// Test-only convenience shim for effect-row unification.
    ///
    /// Effect rows are unified by delegating to the same Rémy row solver.
    #[cfg(test)]
    pub fn unify_effect_rows(
        &mut self,
        expected: &kea_types::EffectRow,
        actual: &kea_types::EffectRow,
        provenance: &Provenance,
    ) {
        self.unify_rows(expected.as_row(), actual.as_row(), provenance);
    }

    /// Add a lacks constraint through the centralized constraint executor.
    ///
    /// Test-only convenience shim. Production inference code should emit
    /// lacks constraints through `constrain(...)` (or typeck helpers) instead.
    #[cfg(test)]
    pub fn constrain_lacks(&mut self, var: RowVarId, label: Label, provenance: &Provenance) {
        self.constrain(Constraint::Lacks {
            var,
            label,
            provenance: provenance.clone(),
        });
    }

    /// Immediate row-unification executor used by the solver core.
    ///
    /// Unifying `{x: Int | r1}` with `{y: Bool | r2}` produces:
    ///   r1 ~ {y: Bool | r3}
    ///   r2 ~ {x: Int | r3}
    /// where r3 is fresh, and r3 lacks both x and y.
    fn unify_rows_immediate(
        &mut self,
        expected: &RowType,
        actual: &RowType,
        provenance: &Provenance,
    ) {
        let expected = self.substitution.apply_row(expected);
        let actual = self.substitution.apply_row(actual);

        // Partition fields into common (same label), only-in-expected, only-in-actual.
        let mut common = Vec::new();
        let mut only_expected = Vec::new();
        let mut only_actual = Vec::new();

        let mut ei = 0;
        let mut ai = 0;
        while ei < expected.fields.len() && ai < actual.fields.len() {
            match expected.fields[ei].0.cmp(&actual.fields[ai].0) {
                std::cmp::Ordering::Equal => {
                    common.push((
                        expected.fields[ei].0.clone(),
                        expected.fields[ei].1.clone(),
                        actual.fields[ai].1.clone(),
                    ));
                    ei += 1;
                    ai += 1;
                }
                std::cmp::Ordering::Less => {
                    only_expected.push(expected.fields[ei].clone());
                    ei += 1;
                }
                std::cmp::Ordering::Greater => {
                    only_actual.push(actual.fields[ai].clone());
                    ai += 1;
                }
            }
        }
        only_expected.extend_from_slice(&expected.fields[ei..]);
        only_actual.extend_from_slice(&actual.fields[ai..]);

        // Unify common fields.
        for (label, exp_ty, act_ty) in &common {
            let field_prov = Provenance {
                span: provenance.span,
                reason: Reason::RecordField {
                    label: label.clone(),
                },
            };
            self.unify_immediate(exp_ty, act_ty, &field_prov);
        }

        match (expected.rest, actual.rest) {
            // Both closed: extra fields on either side are errors.
            (None, None) => {
                for (label, _) in &only_expected {
                    self.errors.push(missing_field_diag(
                        label,
                        &actual.fields,
                        &provenance.reason,
                        provenance.span,
                    ));
                }
                for (label, _) in &only_actual {
                    self.errors.push(extra_field_diag(
                        label,
                        &expected.fields,
                        &provenance.reason,
                        provenance.span,
                    ));
                }
            }

            // Expected is open, actual is closed: bind expected's tail to actual's extra fields.
            (Some(r), None) => {
                // Check lacks constraints for fields being added.
                for (label, _) in &only_actual {
                    if !self.lacks.can_extend(r, label) {
                        self.errors.push(lacks_violation_diag(
                            label,
                            &provenance.reason,
                            provenance.span,
                        ));
                    }
                }
                self.push_unify_step(
                    crate::trace::UnifyAction::BindRowVar,
                    &Type::Row(expected.clone()),
                    &Type::Row(actual.clone()),
                    format!("r{} := closed({})", r.0, only_actual.len()),
                );
                self.substitution.bind_row(r, RowType::closed(only_actual));
                // Expected's extra fields must not exist in actual (it's closed).
                for (label, _) in &only_expected {
                    self.errors.push(missing_field_diag(
                        label,
                        &actual.fields,
                        &provenance.reason,
                        provenance.span,
                    ));
                }
            }

            // Expected is closed, actual is open: mirror of above.
            (None, Some(r)) => {
                for (label, _) in &only_expected {
                    if !self.lacks.can_extend(r, label) {
                        self.errors.push(lacks_violation_diag(
                            label,
                            &provenance.reason,
                            provenance.span,
                        ));
                    }
                }
                self.push_unify_step(
                    crate::trace::UnifyAction::BindRowVar,
                    &Type::Row(expected.clone()),
                    &Type::Row(actual.clone()),
                    format!("r{} := closed({})", r.0, only_expected.len()),
                );
                self.substitution
                    .bind_row(r, RowType::closed(only_expected));
                for (label, _) in &only_actual {
                    self.errors.push(extra_field_diag(
                        label,
                        &expected.fields,
                        &provenance.reason,
                        provenance.span,
                    ));
                }
            }

            // Both open: Rémy decomposition.
            (Some(r1), Some(r2)) if r1 == r2 => {
                // Same row variable: extra fields on either side are errors.
                for (label, _) in &only_expected {
                    self.errors.push(missing_field_diag(
                        label,
                        &actual.fields,
                        &provenance.reason,
                        provenance.span,
                    ));
                }
                for (label, _) in &only_actual {
                    self.errors.push(extra_field_diag(
                        label,
                        &expected.fields,
                        &provenance.reason,
                        provenance.span,
                    ));
                }
            }

            (Some(r1), Some(r2)) => {
                // Different row variables: Rémy-style decomposition.
                //
                // Snapshot r1/r2 lacks BEFORE transfer, since transfer
                // removes from the source. We need the original constraints
                // to check whether r1 can accept only_actual fields (and
                // r2 can accept only_expected fields).
                let r1_lacks = self.lacks.get(r1).cloned();
                let r2_lacks = self.lacks.get(r2).cloned();

                // Check that r1 can accept only_actual fields.
                if let Some(ref labels) = r1_lacks {
                    for (label, _) in &only_actual {
                        if labels.contains(label) {
                            self.errors.push(lacks_violation_diag(
                                label,
                                &provenance.reason,
                                provenance.span,
                            ));
                        }
                    }
                }
                // Check that r2 can accept only_expected fields.
                if let Some(ref labels) = r2_lacks {
                    for (label, _) in &only_expected {
                        if labels.contains(label) {
                            self.errors.push(lacks_violation_diag(
                                label,
                                &provenance.reason,
                                provenance.span,
                            ));
                        }
                    }
                }

                // Create fresh row variable r3 for the shared unknown tail.
                let r3 = self.fresh_row_var();

                self.push_unify_step(
                    crate::trace::UnifyAction::RemyDecompose,
                    &Type::Row(expected.clone()),
                    &Type::Row(actual.clone()),
                    format!(
                        "Rémy: r{} ~ {{only_actual | r{}}}, r{} ~ {{only_expected | r{}}}",
                        r1.0, r3.0, r2.0, r3.0
                    ),
                );

                // r1 ~ {only_actual_fields | r3}
                // r2 ~ {only_expected_fields | r3}

                // Transfer lacks constraints: r3 must lack everything r1 and r2 lack,
                // plus all common labels and the new labels being bound.
                self.lacks.transfer(r1, r3);
                self.lacks.transfer(r2, r3);

                // r3 must lack all labels that appear in either side.
                for (label, _) in expected.fields.iter().chain(actual.fields.iter()) {
                    self.lacks.add(r3, label.clone());
                }

                self.substitution
                    .bind_row(r1, RowType::open(only_actual, r3));
                self.substitution
                    .bind_row(r2, RowType::open(only_expected, r3));
            }
        }
    }

    /// Check whether a type variable occurs in a type (occurs check).
    /// Prevents infinite types like `T = List(T)`.
    fn occurs_in(&self, var: TypeVarId, ty: &Type) -> bool {
        let ty = self.substitution.apply(ty);
        match &ty {
            Type::Var(v) => *v == var,
            Type::List(inner)
            | Type::Set(inner)
            | Type::Option(inner)
            | Type::FixedSizeList { element: inner, .. }
            | Type::Tensor { element: inner, .. } => self.occurs_in(var, inner),
            Type::Map(k, v) | Type::Result(k, v) => {
                self.occurs_in(var, k) || self.occurs_in(var, v)
            }
            Type::Existential {
                associated_types, ..
            } => associated_types.values().any(|t| self.occurs_in(var, t)),
            Type::Tuple(elems) => elems.iter().any(|t| self.occurs_in(var, t)),
            Type::Function(ft) => {
                ft.params.iter().any(|t| self.occurs_in(var, t)) || self.occurs_in(var, &ft.ret)
            }
            Type::Forall(scheme) => {
                if scheme.type_vars.contains(&var) {
                    false
                } else {
                    self.occurs_in(var, &scheme.ty)
                }
            }
            Type::Record(rt) => rt.row.fields.iter().any(|(_, t)| self.occurs_in(var, t)),
            Type::Opaque { params, .. } => params.iter().any(|t| self.occurs_in(var, t)),
            Type::AnonRecord(row) | Type::Row(row) => {
                row.fields.iter().any(|(_, t)| self.occurs_in(var, t))
            }
            Type::Tagged { inner, .. }
            | Type::Stream(inner)
            | Type::Task(inner)
            | Type::Actor(inner)
            | Type::Arc(inner) => self.occurs_in(var, inner),
            Type::App(constructor, args) => {
                self.occurs_in(var, constructor) || args.iter().any(|a| self.occurs_in(var, a))
            }
            Type::Constructor { fixed_args, .. } => {
                fixed_args.iter().any(|(_, ty)| self.occurs_in(var, ty))
            }
            _ => false,
        }
    }

    /// Bind a type variable to a type, with occurs check.
    fn bind_type_var(&mut self, var: TypeVarId, ty: &Type, provenance: &Provenance) {
        if let Type::Var(v) = ty
            && *v == var
        {
            return; // Binding a var to itself is a no-op.
        }

        if self.occurs_in(var, ty) {
            self.push_unify_step(
                crate::trace::UnifyAction::OccursCheck,
                &Type::Var(var),
                ty,
                format!(
                    "t{} occurs in {} — infinite type prevented",
                    var.0,
                    kea_types::sanitize_type_display(ty)
                ),
            );
            self.errors.push(
                Diagnostic::error(
                    Category::TypeError,
                    "infinite type detected (a type cannot contain itself)",
                )
                .at(span_to_location(provenance.span)),
            );
            return;
        }

        self.substitution.bind_type(var, ty.clone());
    }

    /// Push a diagnostic error.
    pub fn push_error(&mut self, diag: Diagnostic) {
        self.errors.push(diag);
    }

    /// Clear errors (for reuse in tests).
    pub fn clear_errors(&mut self) {
        self.errors.clear();
    }

    /// Register a trait bound on a type variable.
    ///
    /// During instantiation, trait bounds from the scheme transfer to fresh
    /// type vars. After inference resolves them to concrete types,
    /// `check_trait_bounds` verifies satisfaction.
    pub fn add_trait_bound(&mut self, var: TypeVarId, trait_name: String) {
        self.add_trait_bound_with_span(var, trait_name, Span::synthetic());
    }

    /// Register a trait bound on a type variable with source provenance.
    pub fn add_trait_bound_with_span(&mut self, var: TypeVarId, trait_name: String, span: Span) {
        self.trait_bounds
            .entry(var)
            .or_default()
            .insert(trait_name.clone());
        let key = (var, trait_name);
        let should_replace = self
            .trait_bound_spans
            .get(&key)
            .is_some_and(|existing| *existing == Span::synthetic() && span != Span::synthetic());
        if should_replace {
            self.trait_bound_spans.insert(key, span);
            return;
        }
        self.trait_bound_spans.entry(key).or_insert(span);
    }

    /// Record that a call-like expression at `span` may need trait evidence
    /// for type variables appearing in `ty`.
    ///
    /// Resolution to concrete `(Trait, Type)` pairs is deferred until
    /// `check_trait_bounds`, after all unification constraints have been applied.
    pub fn note_evidence_site(&mut self, span: Span, ty: &Type) {
        let vars = free_type_vars(ty);
        if vars.is_empty() {
            return;
        }
        self.pending_evidence_sites
            .entry(span)
            .or_default()
            .extend(vars);
    }

    /// Mark entering a lambda body during inference.
    pub fn enter_lambda(&mut self) {
        self.lambda_depth += 1;
    }

    /// Mark exiting a lambda body during inference.
    pub fn exit_lambda(&mut self) {
        self.lambda_depth = self.lambda_depth.saturating_sub(1);
    }

    fn expand_evidence(
        trait_name: &str,
        ty: &Type,
        trait_registry: &crate::typeck::TraitRegistry,
        sites: &mut std::collections::BTreeSet<crate::typeck::EvidenceSite>,
        seen: &mut std::collections::BTreeSet<String>,
    ) {
        // Existentials carry their own packed evidence and do not produce
        // runtime evidence-site requirements.
        if matches!(ty, Type::Existential { .. }) {
            return;
        }

        let Some(candidate) = (match Self::trait_impl_status(trait_registry, trait_name, ty) {
            TraitImplStatus::Unique(candidate) => Some(candidate),
            // Ambiguous trait evidence cannot be expanded soundly.
            TraitImplStatus::Ambiguous => None,
            TraitImplStatus::NoMatch => None,
        }) else {
            return;
        };

        // Recurse once per fully-instantiated goal type so nested bounds on
        // the same constructor at different type arguments still expand.
        let key = format!("{trait_name}::{ty}");
        if !seen.insert(key) {
            return;
        }

        sites.insert(crate::typeck::EvidenceSite {
            trait_name: trait_name.to_string(),
            type_name: candidate.type_name.clone(),
            associated_types: candidate
                .associated_types
                .iter()
                .map(|(name, ty)| (name.clone(), ty.to_string()))
                .collect(),
        });

        for (bound_trait, bound_ty) in candidate.nested_obligations {
            for required_trait in trait_registry.trait_closure(&bound_trait) {
                Self::expand_evidence(&required_trait, &bound_ty, trait_registry, sites, seen);
            }
        }
    }

    /// Check all accumulated trait bounds against the trait registry.
    ///
    /// For each bound `(type_var, trait_name)`:
    /// - Apply substitution to resolve the type var
    /// - If it resolves to a concrete type, resolve `TraitGoal::Implements`
    /// - If still a variable, skip (will be checked when instantiated later)
    /// - Unsatisfied bounds produce diagnostics
    pub fn check_trait_bounds(&mut self, trait_registry: &crate::typeck::TraitRegistry) {
        let mut deferred_obligations = Vec::new();
        for pending in std::mem::take(&mut self.pending_trait_obligations) {
            let resolved = self.substitution.apply(&pending.ty);
            if let Type::Var(_) = resolved {
                deferred_obligations.push(PendingTraitObligation {
                    ty: resolved,
                    ..pending
                });
                continue;
            }
            match trait_registry.solve_goal(&crate::typeck::TraitGoal::Implements {
                trait_name: pending.trait_name.clone(),
                ty: resolved.clone(),
            }) {
                crate::typeck::SolveOutcome::Unique(_) => {}
                crate::typeck::SolveOutcome::Ambiguous(_) => {
                    self.errors.push(
                        Diagnostic::error(
                            Category::TraitBound,
                            format!(
                                "ambiguous impl resolution for trait `{}` on type `{}`",
                                pending.trait_name, resolved
                            ),
                        )
                        .at(span_to_location(pending.provenance.span))
                        .with_help(
                            "add a more specific type annotation or associated-type constraint to disambiguate",
                        ),
                    );
                }
                crate::typeck::SolveOutcome::NoMatch(reasons) => {
                    let mut help = format!("required by trait obligation `{}`", pending.trait_name);
                    if let Some(detail) = Self::trait_nomatch_detail(&reasons) {
                        help = format!("{help}; {detail}");
                    }
                    self.errors.push(
                        Diagnostic::error(
                            Category::TypeError,
                            format!(
                                "type `{}` does not implement trait `{}`",
                                resolved, pending.trait_name
                            ),
                        )
                        .at(span_to_location(pending.provenance.span))
                        .with_help(help),
                    );
                }
            }
        }
        self.pending_trait_obligations = deferred_obligations;

        let mut deferred_assoc = Vec::new();
        for pending in std::mem::take(&mut self.pending_assoc_equalities) {
            let resolved_base = self.substitution.apply(&pending.base_ty);
            let resolved_rhs = self.substitution.apply(&pending.rhs);
            if let Type::Var(_) = resolved_base {
                deferred_assoc.push(PendingAssocTypeEquality {
                    base_ty: resolved_base,
                    rhs: resolved_rhs,
                    ..pending
                });
                continue;
            }
            match trait_registry.solve_goal(&crate::typeck::TraitGoal::ProjectionEq {
                base_trait: pending.base_trait.clone(),
                base_ty: resolved_base.clone(),
                assoc: pending.assoc.clone(),
                rhs: resolved_rhs.clone(),
            }) {
                crate::typeck::SolveOutcome::Unique(_) => {}
                crate::typeck::SolveOutcome::Ambiguous(_) => {
                    self.errors.push(
                        Diagnostic::error(
                            Category::TraitBound,
                            format!(
                                "ambiguous associated type projection for `{}` on `{}`",
                                pending.assoc, resolved_base
                            ),
                        )
                        .at(span_to_location(pending.provenance.span))
                        .with_help(
                            "add a more specific associated-type annotation to disambiguate",
                        ),
                    );
                }
                crate::typeck::SolveOutcome::NoMatch(reasons) => {
                    let mut help = format!(
                        "required projection: `{}.{}` for trait `{}`",
                        resolved_base, pending.assoc, pending.base_trait
                    );
                    if let Some(detail) = Self::trait_nomatch_detail(&reasons) {
                        help = format!("{help}; {detail}");
                    }
                    self.errors.push(
                        Diagnostic::error(
                            Category::TypeError,
                            format!(
                                "associated type constraint `{}.{}` is unsatisfied",
                                resolved_base, pending.assoc
                            ),
                        )
                        .at(span_to_location(pending.provenance.span))
                        .with_help(help),
                    );
                }
            }
        }
        self.pending_assoc_equalities = deferred_assoc;

        let bounds: Vec<_> = self
            .trait_bounds
            .iter()
            .flat_map(|(tv, traits)| traits.iter().map(move |t| (*tv, t.clone())))
            .collect();

        for (tv, trait_name) in bounds {
            let resolved = self.substitution.apply(&Type::Var(tv));
            if let Type::Var(_) = &resolved {
                // Still polymorphic — bound will be checked on next instantiation.
                continue;
            }
            let bound_span = self
                .trait_bound_spans
                .get(&(tv, trait_name.clone()))
                .copied();
            match trait_registry.solve_goal(&crate::typeck::TraitGoal::Implements {
                trait_name: trait_name.clone(),
                ty: resolved.clone(),
            }) {
                crate::typeck::SolveOutcome::Unique(_) => {}
                crate::typeck::SolveOutcome::Ambiguous(_) => {
                    let mut diag = Diagnostic::error(
                        Category::TraitBound,
                        format!(
                            "ambiguous impl resolution for trait `{trait_name}` on type `{resolved}`"
                        ),
                    )
                    .with_help(
                        "add a more specific type annotation or associated-type constraint to disambiguate",
                    );
                    if let Some(span) = bound_span
                        && span != Span::synthetic()
                    {
                        diag = diag.at(span_to_location(span));
                    }
                    self.errors.push(diag);
                }
                crate::typeck::SolveOutcome::NoMatch(reasons) => {
                    let mut help = format!("required by a `where` bound: `{trait_name}`");
                    if let Some(detail) = Self::trait_nomatch_detail(&reasons) {
                        help = format!("{help}; {detail}");
                    }
                    let mut diag = Diagnostic::error(
                        Category::TypeError,
                        format!("type `{resolved}` does not implement trait `{trait_name}`"),
                    )
                    .with_help(help);
                    if let Some(span) = bound_span
                        && span != Span::synthetic()
                    {
                        diag = diag.at(span_to_location(span));
                    }
                    self.errors.push(diag);
                }
            }
        }

        // Resolve pending runtime evidence sites after final substitution.
        for (span, type_vars) in &self.pending_evidence_sites {
            let mut sites: std::collections::BTreeSet<crate::typeck::EvidenceSite> =
                std::collections::BTreeSet::new();
            let mut seen = std::collections::BTreeSet::new();
            for tv in type_vars {
                let Some(bound_traits) = self.trait_bounds.get(tv) else {
                    continue;
                };
                let resolved = self.substitution.apply(&Type::Var(*tv));
                for trait_name in bound_traits {
                    for required_trait in trait_registry.trait_closure(trait_name) {
                        Self::expand_evidence(
                            &required_trait,
                            &resolved,
                            trait_registry,
                            &mut sites,
                            &mut seen,
                        );
                    }
                }
            }
            if !sites.is_empty() {
                self.type_annotations
                    .evidence_sites
                    .insert(*span, sites.into_iter().collect());
            }
        }
    }

    /// Extract and clear collected runtime type annotations.
    pub fn take_type_annotations(&mut self) -> crate::typeck::TypeAnnotations {
        self.pending_evidence_sites.clear();
        self.pending_trait_obligations.clear();
        self.pending_assoc_equalities.clear();
        self.trait_bound_spans.clear();
        std::mem::take(&mut self.type_annotations)
    }

    /// Set a bidirectional expected type hint for constructor disambiguation.
    pub fn set_bidir_expected(&mut self, expected: Option<Type>) {
        self.bidir_expected_type = expected;
    }

    /// Get the bidirectional expected type hint.
    pub fn bidir_expected(&self) -> Option<&Type> {
        self.bidir_expected_type.as_ref()
    }

    /// Record a resolved variant type name at a span for evaluator dispatch.
    pub fn record_resolved_variant(&mut self, span: Span, type_name: String) {
        self.type_annotations
            .resolved_variants
            .insert(span, type_name);
    }

    /// Solve a set of constraints.
    pub fn solve(&mut self, constraints: Vec<Constraint>) -> Result<(), DiagnosticError> {
        self.solve_with_options(constraints, SolveOptions::default())
    }

    fn apply_constraint(&mut self, constraint: Constraint) {
        match constraint {
            Constraint::TypeEqual {
                expected,
                actual,
                provenance,
            } => self.unify_immediate(&expected, &actual, &provenance),
            Constraint::RowEqual {
                expected,
                actual,
                provenance,
            } => self.unify_rows_immediate(&expected, &actual, &provenance),
            Constraint::Lacks {
                var,
                label,
                provenance,
            } => {
                // Check if the variable is already bound to a row containing this label.
                if let Some(row) = self.substitution.lookup_row(var) {
                    let row = row.clone();
                    if row.has(&label) {
                        self.errors.push(lacks_violation_diag(
                            &label,
                            &provenance.reason,
                            provenance.span,
                        ));
                    }
                }
                self.lacks.add(var, label);
            }
            Constraint::TraitObligation {
                ty,
                trait_name,
                provenance,
            } => {
                let resolved = self.substitution.apply(&ty);
                if let Type::Var(tv) = resolved {
                    self.add_trait_bound_with_span(tv, trait_name, provenance.span);
                } else {
                    self.pending_trait_obligations.push(PendingTraitObligation {
                        ty: resolved,
                        trait_name,
                        provenance,
                    });
                }
            }
            Constraint::AssocTypeEqual {
                base_trait,
                base_ty,
                assoc,
                rhs,
                provenance,
            } => {
                self.pending_assoc_equalities
                    .push(PendingAssocTypeEquality {
                        base_trait,
                        base_ty: self.substitution.apply(&base_ty),
                        assoc,
                        rhs: self.substitution.apply(&rhs),
                        provenance,
                    });
            }
            Constraint::KindEqual {
                expected,
                actual,
                provenance,
            } => {
                if expected != actual {
                    self.errors.push(
                        Diagnostic::error(
                            Category::TypeError,
                            format!("kind mismatch: expected `{expected}`, got `{actual}`"),
                        )
                        .at(span_to_location(provenance.span)),
                    );
                }
            }
        }
    }

    fn solve_with_options(
        &mut self,
        constraints: Vec<Constraint>,
        options: SolveOptions,
    ) -> Result<(), DiagnosticError> {
        let mut recent = std::collections::VecDeque::with_capacity(options.trace_limit.max(1));

        for (iterations, constraint) in constraints.into_iter().enumerate() {
            let (summary, span) = constraint_trace_entry(&constraint);
            if options.trace_limit > 0 {
                if recent.len() == options.trace_limit {
                    recent.pop_front();
                }
                recent.push_back(summary);
            }

            if iterations >= options.max_iterations {
                let trace_help = if recent.is_empty() {
                    "no recent constraints captured".to_string()
                } else {
                    format!(
                        "recent constraints:\n- {}",
                        recent.iter().cloned().collect::<Vec<_>>().join("\n- ")
                    )
                };
                let mut diag = Diagnostic::error(
                    Category::TypeError,
                    "constraint solver exceeded iteration budget".to_string(),
                )
                .with_help(format!(
                    "{trace_help}\nraise `max_iterations` or inspect recursive obligation generation"
                ));
                if let Some(span) = span {
                    diag = diag.at(span_to_location(span));
                }
                self.errors.push(diag);
                break;
            }

            self.apply_constraint(constraint);
        }

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(DiagnosticError::multiple(std::mem::take(&mut self.errors)))
        }
    }

    #[cfg(test)]
    pub(crate) fn solve_with_budget_for_test(
        &mut self,
        constraints: Vec<Constraint>,
        max_iterations: usize,
    ) -> Result<(), DiagnosticError> {
        self.solve_with_options(
            constraints,
            SolveOptions {
                max_iterations,
                trace_limit: 8,
            },
        )
    }

    /// Retrieve accumulated errors without consuming the unifier.
    pub fn errors(&self) -> &[Diagnostic] {
        &self.errors
    }

    /// Check if unification has produced any errors.
    pub fn has_errors(&self) -> bool {
        self.errors
            .iter()
            .any(|diag| matches!(diag.severity, kea_diag::Severity::Error))
    }

    /// Probe whether a set of constraints is satisfiable without mutating the
    /// current solver state.
    pub(crate) fn constraints_satisfiable(&self, constraints: Vec<Constraint>) -> bool {
        let mut probe = self.clone();
        probe.errors.clear();
        probe
            .solve_with_options(
                constraints,
                SolveOptions {
                    max_iterations: 16_384,
                    trace_limit: 0,
                },
            )
            .is_ok()
    }

    // -----------------------------------------------------------------------
    // Tracing API (zero overhead when disabled)
    // -----------------------------------------------------------------------

    /// Enable step-by-step tracing for observability tools.
    pub fn enable_tracing(&mut self) {
        self.tracing = true;
    }

    /// Whether tracing is active.
    pub fn is_tracing(&self) -> bool {
        self.tracing
    }

    /// Get the unification trace (empty if tracing was not enabled).
    pub fn unify_trace(&self) -> &[crate::trace::UnifyStep] {
        &self.unify_trace
    }

    fn push_unify_step(
        &mut self,
        action: crate::trace::UnifyAction,
        left: &Type,
        right: &Type,
        detail: String,
    ) {
        if self.tracing {
            let step_num = self.unify_trace.len() + 1;
            self.unify_trace.push(crate::trace::UnifyStep {
                step: step_num,
                action,
                left: kea_types::sanitize_type_display(left),
                right: kea_types::sanitize_type_display(right),
                detail,
            });
        }
    }
}

impl Default for Unifier {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn constraint_trace_entry(constraint: &Constraint) -> (String, Option<Span>) {
    match constraint {
        Constraint::TypeEqual {
            expected,
            actual,
            provenance,
        } => (
            format!(
                "TypeEq {} ~ {} ({:?})",
                kea_types::sanitize_type_display(expected),
                kea_types::sanitize_type_display(actual),
                provenance.reason
            ),
            Some(provenance.span),
        ),
        Constraint::RowEqual {
            expected,
            actual,
            provenance,
        } => (
            format!(
                "RowEq {} ~ {} ({:?})",
                kea_types::sanitize_type_display(&Type::Row(expected.clone())),
                kea_types::sanitize_type_display(&Type::Row(actual.clone())),
                provenance.reason
            ),
            Some(provenance.span),
        ),
        Constraint::Lacks {
            var,
            label,
            provenance,
        } => (
            format!("Lacks r{} ! {} ({:?})", var.0, label, provenance.reason),
            Some(provenance.span),
        ),
        Constraint::TraitObligation {
            ty,
            trait_name,
            provenance,
        } => (
            format!(
                "TraitObligation {}: {} ({:?})",
                kea_types::sanitize_type_display(ty),
                trait_name,
                provenance.reason
            ),
            Some(provenance.span),
        ),
        Constraint::AssocTypeEqual {
            base_trait,
            base_ty,
            assoc,
            rhs,
            provenance,
        } => (
            format!(
                "AssocTypeEq {}.{} @ {} = {} ({:?})",
                kea_types::sanitize_type_display(base_ty),
                assoc,
                base_trait,
                kea_types::sanitize_type_display(rhs),
                provenance.reason
            ),
            Some(provenance.span),
        ),
        Constraint::KindEqual {
            expected,
            actual,
            provenance,
        } => (
            format!("KindEq {} ~ {} ({:?})", expected, actual, provenance.reason),
            Some(provenance.span),
        ),
    }
}

/// Determine the domain term for row error messages based on provenance.
///
/// Returns (entity, "the entity") — for example ("field", "the record").
fn row_domain(reason: &Reason) -> (&'static str, &'static str) {
    match reason {
        Reason::FunctionArg { .. } | Reason::ReturnType => ("field", "the function"),
        _ => ("field", "the record"),
    }
}

/// Format a list of field labels for display in error messages.
fn format_field_list(fields: &[(Label, Type)]) -> String {
    fields
        .iter()
        .map(|(l, _)| format!("`{l}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Build a missing field diagnostic with context from provenance.
fn missing_field_diag(
    label: &Label,
    expected_fields: &[(Label, Type)],
    reason: &Reason,
    span: Span,
) -> Diagnostic {
    let (field_term, entity) = row_domain(reason);
    let msg = format!("{entity} is missing {field_term} `{label}`");
    let mut diag = Diagnostic::error(Category::MissingField, msg).at(span_to_location(span));
    if !expected_fields.is_empty() {
        diag = diag.with_help(format!(
            "expected {field_term}s: {}",
            format_field_list(expected_fields)
        ));
    }
    diag
}

/// Build an extra field diagnostic with context from provenance.
///
/// For function arguments, an "extra" field on the function side means
/// the argument is *missing* that field, so we phrase it accordingly.
fn extra_field_diag(
    label: &Label,
    expected_fields: &[(Label, Type)],
    reason: &Reason,
    span: Span,
) -> Diagnostic {
    let (field_term, entity) = row_domain(reason);
    match reason {
        Reason::FunctionArg { .. } => {
            let msg = format!("missing {field_term} `{label}` — required by {entity}");
            let mut diag =
                Diagnostic::error(Category::MissingField, msg).at(span_to_location(span));
            if !expected_fields.is_empty() {
                diag = diag.with_help(format!(
                    "available {field_term}s: {}",
                    format_field_list(expected_fields)
                ));
            }
            diag
        }
        _ => {
            let msg = format!("{entity} has unexpected {field_term} `{label}`");
            let mut diag = Diagnostic::error(Category::ExtraField, msg).at(span_to_location(span));
            if !expected_fields.is_empty() {
                diag = diag.with_help(format!(
                    "expected {field_term}s: {}",
                    format_field_list(expected_fields)
                ));
            }
            diag
        }
    }
}

/// Build a lacks-violation (duplicate field) diagnostic with context from provenance.
fn lacks_violation_diag(label: &Label, reason: &Reason, span: Span) -> Diagnostic {
    let (field_term, entity) = row_domain(reason);
    let msg = format!(
        "cannot add {field_term} `{label}` — {entity} already has a {field_term} named `{label}`"
    );
    Diagnostic::error(Category::DuplicateField, msg).at(span_to_location(span))
}

/// Produce a contextual type mismatch message using the Reason provenance.
fn type_mismatch_message(
    expected: &Type,
    actual: &Type,
    reason: &Reason,
) -> (String, Option<String>) {
    let (expected, actual) = kea_types::sanitize_type_pair_display(expected, actual);
    match reason {
        Reason::BinaryOp(op) => (
            format!(
                "both sides of `{op}` must have the same type, but left is `{expected}` and right is `{actual}`"
            ),
            None,
        ),
        Reason::FunctionArg { .. } => (
            format!("type mismatch in function call: expected `{expected}`, got `{actual}`"),
            None,
        ),
        Reason::ReturnType => (
            format!("return type mismatch: expected `{expected}`, got `{actual}`"),
            None,
        ),
        Reason::LetAnnotation => (
            format!(
                "type annotation mismatch: declared `{expected}`, but value has type `{actual}`"
            ),
            None,
        ),
        Reason::TypeAscription => (
            format!("type mismatch in `as` ascription: expected `{expected}`, got `{actual}`"),
            Some("`as` checks compatibility and does not perform runtime conversion".into()),
        ),
        Reason::IfBranches => (
            format!("if/else branches have different types: `{expected}` vs `{actual}`"),
            Some("both branches must have the same type".into()),
        ),
        Reason::RangeBounds => (
            format!("range bounds must have the same type: `{expected}` vs `{actual}`"),
            Some("use matching start/end types (for example `1..10` or `1.0..2.0`)".into()),
        ),
        Reason::CaseArms => (
            format!("case arms have different types: `{expected}` vs `{actual}`"),
            Some("all arms must return the same type".into()),
        ),
        Reason::RecordField { label } => (
            format!("field `{label}` has type `{expected}`, but got `{actual}`"),
            None,
        ),
        Reason::TraitBound { trait_name } => (
            format!("type `{actual}` does not implement trait `{trait_name}`"),
            Some(format!(
                "required because of a `where` bound: `{trait_name}`"
            )),
        ),
        _ => (
            format!("type mismatch: expected `{expected}`, got `{actual}`"),
            None,
        ),
    }
}

fn span_to_location(span: Span) -> SourceLocation {
    SourceLocation {
        file_id: span.file.0,
        start: span.start,
        end: span.end,
    }
}

#[cfg(test)]
mod prop_tests;

#[cfg(test)]
mod typeck_tests;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;
    use kea_ast::FileId;
    use kea_types::{EffectRow, FunctionType, Kind};

    fn test_span() -> Span {
        Span::new(FileId(0), 0, 1)
    }

    fn test_prov() -> Provenance {
        Provenance {
            span: test_span(),
            reason: Reason::LetAnnotation,
        }
    }

    #[test]
    fn type_mismatch_message_uses_joint_sanitization() {
        let expected = Type::Function(FunctionType {
            params: vec![Type::Int, Type::Int],
            ret: Box::new(Type::Var(TypeVarId(1))),
            effects: EffectRow::pure(),
        });
        let actual = Type::Function(FunctionType {
            params: vec![Type::Var(TypeVarId(0))],
            ret: Box::new(Type::Var(TypeVarId(0))),
            effects: EffectRow::pure(),
        });

        let (message, _) =
            type_mismatch_message(&expected, &actual, &Reason::FunctionArg { param_index: 0 });

        assert_eq!(
            message,
            "type mismatch in function call: expected `(Int, Int) -> b`, got `(a) -> a`"
        );
    }

    #[test]
    fn unify_identical_types() {
        let mut u = Unifier::new();
        u.unify(&Type::Int, &Type::Int, &test_prov());
        assert!(!u.has_errors());
    }

    #[test]
    fn unify_type_mismatch() {
        let mut u = Unifier::new();
        u.unify(&Type::Int, &Type::String, &test_prov());
        assert!(u.has_errors());
        assert_eq!(u.errors().len(), 1);
    }

    #[test]
    fn has_errors_ignores_warning_diagnostics() {
        let mut u = Unifier::new();
        u.push_error(Diagnostic::warning(
            Category::TypeMismatch,
            "warning-only diagnostic",
        ));
        assert!(!u.has_errors());
        assert_eq!(u.errors().len(), 1);
    }

    #[test]
    fn trait_nomatch_detail_formats_fundep_conflict() {
        let reasons = vec![crate::typeck::MismatchReason::FundepConflict {
            dependency: "Self -> Item".to_string(),
        }];
        assert_eq!(
            Unifier::trait_nomatch_detail(&reasons),
            Some("functional dependency conflict while solving `Self -> Item`".to_string())
        );
    }

    #[test]
    fn trait_nomatch_detail_ignores_unknown_trait_reason() {
        let reasons = vec![crate::typeck::MismatchReason::UnknownTrait {
            trait_name: "Missing".to_string(),
        }];
        assert_eq!(Unifier::trait_nomatch_detail(&reasons), None);
    }

    #[test]
    fn unify_type_var_binds() {
        let mut u = Unifier::new();
        let var = TypeVarId(0);
        u.unify(&Type::Var(var), &Type::Int, &test_prov());
        assert!(!u.has_errors());
        assert_eq!(u.substitution.apply(&Type::Var(var)), Type::Int);
    }

    #[test]
    fn unify_transitive() {
        let mut u = Unifier::new();
        let a = TypeVarId(0);
        let b = TypeVarId(1);
        u.unify(&Type::Var(a), &Type::Var(b), &test_prov());
        u.unify(&Type::Var(b), &Type::Int, &test_prov());
        assert!(!u.has_errors());
        assert_eq!(u.substitution.apply(&Type::Var(a)), Type::Int);
    }

    #[test]
    fn unify_dim_var_binds_known() {
        let mut u = Unifier::new();
        let d = u.fresh_dim_var();
        u.unify_dim(&Dim::Var(d), &Dim::Known(128), &test_prov());
        assert_eq!(u.resolve_dim(&Dim::Var(d)), Dim::Known(128));
    }

    #[test]
    fn unify_dim_mismatch_errors() {
        let mut u = Unifier::new();
        u.unify_dim(&Dim::Known(32), &Dim::Known(64), &test_prov());
        assert!(u.has_errors(), "dimension mismatch should be reported");
    }

    #[test]
    fn unify_decimal_unifies_precision_and_scale_dims() {
        let mut u = Unifier::new();
        let p = u.fresh_dim_var();
        let s = u.fresh_dim_var();
        let left = Type::Decimal {
            precision: Dim::Var(p),
            scale: Dim::Var(s),
        };
        let right = Type::Decimal {
            precision: Dim::Known(18),
            scale: Dim::Known(2),
        };

        u.unify(&left, &right, &test_prov());

        assert!(
            !u.has_errors(),
            "decimal dimensions should unify cleanly: {:?}",
            u.errors()
        );
        assert_eq!(u.resolve_dim(&Dim::Var(p)), Dim::Known(18));
        assert_eq!(u.resolve_dim(&Dim::Var(s)), Dim::Known(2));
    }

    #[test]
    fn unify_decimal_scale_mismatch_reports_error() {
        let mut u = Unifier::new();
        let left = Type::Decimal {
            precision: Dim::Known(18),
            scale: Dim::Known(2),
        };
        let right = Type::Decimal {
            precision: Dim::Known(18),
            scale: Dim::Known(4),
        };

        u.unify(&left, &right, &test_prov());

        assert!(
            u.has_errors(),
            "decimal scale mismatch should fail unification"
        );
    }

    #[test]
    fn unify_fixed_size_list_unifies_element_and_size_dims() {
        let mut u = Unifier::new();
        let d = u.fresh_dim_var();
        let left = Type::FixedSizeList {
            element: Box::new(Type::Var(TypeVarId(0))),
            size: Dim::Var(d),
        };
        let right = Type::FixedSizeList {
            element: Box::new(Type::Int),
            size: Dim::Known(768),
        };

        u.unify(&left, &right, &test_prov());

        assert!(!u.has_errors(), "fixed-size list should unify cleanly");
        assert_eq!(u.substitution.apply(&Type::Var(TypeVarId(0))), Type::Int);
        assert_eq!(u.resolve_dim(&Dim::Var(d)), Dim::Known(768));
    }

    #[test]
    fn unify_tensor_unifies_element_and_shape_dims() {
        let mut u = Unifier::new();
        let m = u.fresh_dim_var();
        let n = u.fresh_dim_var();
        let left = Type::Tensor {
            element: Box::new(Type::Var(TypeVarId(0))),
            shape: vec![Dim::Var(m), Dim::Var(n)],
        };
        let right = Type::Tensor {
            element: Box::new(Type::Float),
            shape: vec![Dim::Known(32), Dim::Known(784)],
        };

        u.unify(&left, &right, &test_prov());

        assert!(!u.has_errors(), "tensor dimensions should unify cleanly");
        assert_eq!(u.substitution.apply(&Type::Var(TypeVarId(0))), Type::Float);
        assert_eq!(u.resolve_dim(&Dim::Var(m)), Dim::Known(32));
        assert_eq!(u.resolve_dim(&Dim::Var(n)), Dim::Known(784));
    }

    #[test]
    fn unify_tensor_rank_mismatch_reports_error() {
        let mut u = Unifier::new();
        let left = Type::Tensor {
            element: Box::new(Type::Float),
            shape: vec![Dim::Known(32), Dim::Known(784)],
        };
        let right = Type::Tensor {
            element: Box::new(Type::Float),
            shape: vec![Dim::Known(32)],
        };

        u.unify(&left, &right, &test_prov());

        assert!(
            u.has_errors(),
            "tensor rank mismatch should report an error"
        );
        assert!(
            u.errors()
                .iter()
                .any(|diag| diag.message.contains("tensor rank mismatch")),
            "expected tensor rank mismatch diagnostic, got {:?}",
            u.errors()
        );
    }

    #[test]
    fn unify_forall_alpha_equivalent_succeeds() {
        let mut u = Unifier::new();
        let left = Type::Forall(Box::new(TypeScheme {
            type_vars: vec![TypeVarId(7)],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: BTreeMap::new(),
            ty: Type::Function(FunctionType {
                params: vec![Type::Var(TypeVarId(7))],
                ret: Box::new(Type::Var(TypeVarId(7))),
                effects: EffectRow::pure(),
            }),
        }));
        let right = Type::Forall(Box::new(TypeScheme {
            type_vars: vec![TypeVarId(42)],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: BTreeMap::new(),
            ty: Type::Function(FunctionType {
                params: vec![Type::Var(TypeVarId(42))],
                ret: Box::new(Type::Var(TypeVarId(42))),
                effects: EffectRow::pure(),
            }),
        }));

        u.unify(&left, &right, &test_prov());
        assert!(
            !u.has_errors(),
            "alpha-equivalent forall schemes should unify: {:?}",
            u.errors()
        );
    }

    #[test]
    fn unify_forall_distinct_bounds_fails() {
        let mut u = Unifier::new();
        let mut left_bounds = BTreeMap::new();
        left_bounds.insert(TypeVarId(1), BTreeSet::from([String::from("Show")]));
        let mut right_bounds = BTreeMap::new();
        right_bounds.insert(TypeVarId(9), BTreeSet::from([String::from("Eq")]));

        let left = Type::Forall(Box::new(TypeScheme {
            type_vars: vec![TypeVarId(1)],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: left_bounds,
            kinds: BTreeMap::new(),
            ty: Type::Var(TypeVarId(1)),
        }));
        let right = Type::Forall(Box::new(TypeScheme {
            type_vars: vec![TypeVarId(9)],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: right_bounds,
            kinds: BTreeMap::new(),
            ty: Type::Var(TypeVarId(9)),
        }));

        u.unify(&left, &right, &test_prov());
        assert!(
            u.has_errors(),
            "forall schemes with different bounds must fail"
        );
    }

    #[test]
    fn forall_alpha_equivalence_handles_identity_quantified_ids() {
        let scheme = TypeScheme {
            type_vars: vec![TypeVarId(0)],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: BTreeMap::new(),
            ty: Type::Var(TypeVarId(0)),
        };
        assert!(alpha_equivalent_type_schemes(&scheme, &scheme));
    }

    #[test]
    fn constructor_placeholder_satisfies_kinded_trait_bound() {
        let mut registry = crate::typeck::TraitRegistry::new();
        let records = crate::typeck::RecordRegistry::new();
        let span = test_span();
        let sp = |s: &str| kea_ast::Spanned::new(s.to_string(), span);

        let trait_def = kea_ast::TraitDef {
            public: true,
            name: sp("Applicative"),
            doc: None,
            type_params: vec![kea_ast::TraitTypeParam {
                name: sp("F"),
                kind: kea_ast::KindAnnotation::Star,
            }],
            supertraits: vec![],
            fundeps: vec![],
            associated_types: vec![],
            methods: vec![],
        };
        registry.register_trait(&trait_def, &records).unwrap();

        let impl_block = kea_ast::ImplBlock {
            trait_name: sp("Applicative"),
            type_name: sp("Option"),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![],
        };
        registry.register_trait_impl(&impl_block).unwrap();
        registry.add_impl_methods(BTreeMap::new()).unwrap();

        let mut u = Unifier::new();
        let f = u.fresh_type_var_with_kind(Kind::Star);
        u.add_trait_bound(f, "Applicative".to_string());
        u.unify(
            &Type::Var(f),
            &Type::Constructor {
                name: "Option".to_string(),
                fixed_args: vec![],
                arity: 1,
            },
            &test_prov(),
        );
        assert!(!u.has_errors(), "unexpected unify errors: {:?}", u.errors());
        u.check_trait_bounds(&registry);
        assert!(
            !u.has_errors(),
            "constructor placeholder should satisfy Applicative: {:?}",
            u.errors()
        );
    }

    #[test]
    fn constructor_placeholder_emits_runtime_evidence_site() {
        let mut registry = crate::typeck::TraitRegistry::new();
        let records = crate::typeck::RecordRegistry::new();
        let span = test_span();
        let sp = |s: &str| kea_ast::Spanned::new(s.to_string(), span);

        let trait_def = kea_ast::TraitDef {
            public: true,
            name: sp("Applicative"),
            doc: None,
            type_params: vec![kea_ast::TraitTypeParam {
                name: sp("F"),
                kind: kea_ast::KindAnnotation::Star,
            }],
            supertraits: vec![],
            fundeps: vec![],
            associated_types: vec![],
            methods: vec![],
        };
        registry.register_trait(&trait_def, &records).unwrap();

        let impl_block = kea_ast::ImplBlock {
            trait_name: sp("Applicative"),
            type_name: sp("Option"),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![],
        };
        registry.register_trait_impl(&impl_block).unwrap();
        registry.add_impl_methods(BTreeMap::new()).unwrap();

        let mut u = Unifier::new();
        let f = u.fresh_type_var_with_kind(Kind::Star);
        u.add_trait_bound(f, "Applicative".to_string());
        u.note_evidence_site(span, &Type::Var(f));
        u.unify(
            &Type::Var(f),
            &Type::Constructor {
                name: "Option".to_string(),
                fixed_args: vec![],
                arity: 1,
            },
            &test_prov(),
        );
        u.check_trait_bounds(&registry);
        assert!(
            !u.has_errors(),
            "unexpected trait-bound errors: {:?}",
            u.errors()
        );
        let sites = u
            .type_annotations
            .evidence_sites
            .get(&span)
            .cloned()
            .unwrap_or_default();
        assert!(
            sites
                .iter()
                .any(|site| site.trait_name == "Applicative" && site.type_name == "Option"),
            "expected Applicative/Option evidence at span, got {:?}",
            sites
        );
    }

    #[test]
    fn unify_compound_types() {
        let mut u = Unifier::new();
        let var = TypeVarId(0);
        let expected = Type::List(Box::new(Type::Var(var)));
        let actual = Type::List(Box::new(Type::Int));
        u.unify(&expected, &actual, &test_prov());
        assert!(!u.has_errors());
        assert_eq!(u.substitution.apply(&Type::Var(var)), Type::Int);
    }

    #[test]
    fn unify_constructor_application_option_binds_constructor_var() {
        let mut u = Unifier::new();
        let f = u.fresh_type_var();
        let a = u.fresh_type_var();
        let expected = Type::App(Box::new(Type::Var(f)), vec![Type::Var(a)]);
        let actual = Type::Option(Box::new(Type::Int));

        u.unify(&expected, &actual, &test_prov());
        assert!(!u.has_errors());
        assert_eq!(u.substitution.apply(&Type::Var(a)), Type::Int);
        assert_eq!(
            u.substitution.apply(&Type::Var(f)),
            Type::Constructor {
                name: "Option".to_string(),
                fixed_args: vec![],
                arity: 1,
            }
        );
    }

    #[test]
    fn unify_constructor_application_result_binds_partial_constructor() {
        let mut u = Unifier::new();
        let f = u.fresh_type_var();
        let a = u.fresh_type_var();
        let expected = Type::App(Box::new(Type::Var(f)), vec![Type::Var(a)]);
        let actual = Type::Result(Box::new(Type::Int), Box::new(Type::String));

        u.unify(&expected, &actual, &test_prov());
        assert!(!u.has_errors());
        assert_eq!(u.substitution.apply(&Type::Var(a)), Type::Int);
        assert_eq!(
            u.substitution.apply(&Type::Var(f)),
            Type::Constructor {
                name: "Result".to_string(),
                fixed_args: vec![(1, Type::String)],
                arity: 2,
            }
        );
    }

    #[test]
    fn unify_stream_types() {
        let mut u = Unifier::new();
        let var = TypeVarId(0);
        let expected = Type::Stream(Box::new(Type::Var(var)));
        let actual = Type::Stream(Box::new(Type::Int));
        u.unify(&expected, &actual, &test_prov());
        assert!(!u.has_errors());
        assert_eq!(u.substitution.apply(&Type::Var(var)), Type::Int);
    }

    #[test]
    fn unify_function_types() {
        let mut u = Unifier::new();
        let var = TypeVarId(0);
        let expected = Type::Function(FunctionType {
            params: vec![Type::Var(var)],
            ret: Box::new(Type::Bool),
            effects: EffectRow::pure(),
        });
        let actual = Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Bool),
            effects: EffectRow::pure(),
        });
        u.unify(&expected, &actual, &test_prov());
        assert!(!u.has_errors());
        assert_eq!(u.substitution.apply(&Type::Var(var)), Type::Int);
    }

    #[test]
    fn dynamic_widening_ok_narrowing_errors() {
        // Widening: expected=Dynamic, actual=Int → OK (losing type info)
        let mut widen = Unifier::new();
        widen.unify(&Type::Dynamic, &Type::Int, &test_prov());
        assert!(!widen.has_errors());

        // Narrowing: expected=Int, actual=Dynamic → ERROR (needs explicit assertion)
        let mut narrow = Unifier::new();
        narrow.unify(&Type::Int, &Type::Dynamic, &test_prov());
        assert!(narrow.has_errors());
        let err = &narrow.errors[0];
        assert!(err.message.contains("Dynamic"));

        // Dynamic to Dynamic: always OK
        let mut same = Unifier::new();
        same.unify(&Type::Dynamic, &Type::Dynamic, &test_prov());
        assert!(!same.has_errors());
    }

    #[test]
    fn unify_existential_associated_types() {
        let mut u = Unifier::new();
        let mut a = BTreeMap::new();
        let mut b = BTreeMap::new();
        a.insert("Item".to_string(), Type::Var(TypeVarId(0)));
        b.insert("Item".to_string(), Type::Int);
        let left = Type::Existential {
            bounds: vec!["Show".to_string()],
            associated_types: a,
        };
        let right = Type::Existential {
            bounds: vec!["Show".to_string()],
            associated_types: b,
        };

        u.unify(&left, &right, &test_prov());
        assert!(!u.has_errors());
        assert_eq!(u.substitution.apply(&Type::Var(TypeVarId(0))), Type::Int);
    }

    #[test]
    fn unify_existential_bound_mismatch_errors() {
        let mut u = Unifier::new();
        let left = Type::Existential {
            bounds: vec!["Show".to_string()],
            associated_types: BTreeMap::new(),
        };
        let right = Type::Existential {
            bounds: vec!["Eq".to_string()],
            associated_types: BTreeMap::new(),
        };

        u.unify(&left, &right, &test_prov());
        assert!(u.has_errors());
    }

    #[test]
    fn occurs_check_prevents_infinite_type() {
        let mut u = Unifier::new();
        let var = TypeVarId(0);
        // Try to unify T with List(T) — should fail.
        u.unify(
            &Type::Var(var),
            &Type::List(Box::new(Type::Var(var))),
            &test_prov(),
        );
        assert!(u.has_errors());
        assert!(u.errors()[0].message.contains("infinite type"));
    }

    #[test]
    fn unify_closed_rows_same_fields() {
        let mut u = Unifier::new();
        let r1 = RowType::closed(vec![
            (Label::new("name"), Type::String),
            (Label::new("age"), Type::Int),
        ]);
        let r2 = RowType::closed(vec![
            (Label::new("name"), Type::String),
            (Label::new("age"), Type::Int),
        ]);
        u.unify_rows(&r1, &r2, &test_prov());
        assert!(!u.has_errors());
    }

    #[test]
    fn unify_closed_rows_different_types() {
        let mut u = Unifier::new();
        let r1 = RowType::closed(vec![(Label::new("x"), Type::Int)]);
        let r2 = RowType::closed(vec![(Label::new("x"), Type::String)]);
        u.unify_rows(&r1, &r2, &test_prov());
        assert!(u.has_errors());
    }

    #[test]
    fn unify_closed_rows_missing_field() {
        let mut u = Unifier::new();
        let r1 = RowType::closed(vec![
            (Label::new("x"), Type::Int),
            (Label::new("y"), Type::Bool),
        ]);
        let r2 = RowType::closed(vec![(Label::new("x"), Type::Int)]);
        u.unify_rows(&r1, &r2, &test_prov());
        assert!(u.has_errors());
    }

    #[test]
    fn unify_open_row_binds_tail() {
        let mut u = Unifier::new();
        let r_var = RowVarId(0);
        // {name: String | r} unified with {name: String, age: Int}
        let r1 = RowType::open(vec![(Label::new("name"), Type::String)], r_var);
        let r2 = RowType::closed(vec![
            (Label::new("age"), Type::Int),
            (Label::new("name"), Type::String),
        ]);
        u.unify_rows(&r1, &r2, &test_prov());
        assert!(!u.has_errors());

        // r_var should now be bound to {age: Int}.
        let resolved = u.substitution.lookup_row(r_var).unwrap();
        assert!(resolved.is_closed());
        assert!(resolved.has(&Label::new("age")));
    }

    #[test]
    fn unify_effect_rows_same_effects() {
        let mut u = Unifier::new();
        let e1 = kea_types::EffectRow::closed(vec![
            (Label::new("Fail"), Type::String),
            (Label::new("IO"), Type::Unit),
        ]);
        let e2 = kea_types::EffectRow::closed(vec![
            (Label::new("IO"), Type::Unit),
            (Label::new("Fail"), Type::String),
        ]);
        u.unify_effect_rows(&e1, &e2, &test_prov());
        assert!(!u.has_errors());
    }

    #[test]
    fn unify_effect_rows_payload_mismatch_errors() {
        let mut u = Unifier::new();
        let expected = kea_types::EffectRow::closed(vec![(Label::new("Fail"), Type::String)]);
        let actual = kea_types::EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]);
        u.unify_effect_rows(&expected, &actual, &test_prov());
        assert!(u.has_errors());
    }

    #[test]
    fn unify_open_effect_row_binds_tail() {
        let mut u = Unifier::new();
        let tail = RowVarId(33);
        let open = kea_types::EffectRow::open(vec![(Label::new("IO"), Type::Unit)], tail);
        let closed = kea_types::EffectRow::closed(vec![
            (Label::new("IO"), Type::Unit),
            (Label::new("Fail"), Type::String),
        ]);
        u.unify_effect_rows(&open, &closed, &test_prov());
        assert!(!u.has_errors());

        let resolved = u.substitution.lookup_row(tail).unwrap();
        assert!(resolved.is_closed());
        assert!(resolved.has(&Label::new("Fail")));
    }

    #[test]
    fn remy_decomposition_both_open() {
        let mut u = Unifier::new();
        let r1 = RowVarId(100);
        let r2 = RowVarId(101);

        // {x: Int | r1} unified with {y: Bool | r2}
        // Should produce r1 ~ {y: Bool | r3}, r2 ~ {x: Int | r3}
        let row1 = RowType::open(vec![(Label::new("x"), Type::Int)], r1);
        let row2 = RowType::open(vec![(Label::new("y"), Type::Bool)], r2);
        u.unify_rows(&row1, &row2, &test_prov());
        assert!(!u.has_errors());

        // r1 should be bound to {y: Bool | r3} for some r3.
        let r1_resolved = u.substitution.lookup_row(r1).unwrap();
        assert!(r1_resolved.has(&Label::new("y")));
        assert!(r1_resolved.is_open());

        // r2 should be bound to {x: Int | r3} for same r3.
        let r2_resolved = u.substitution.lookup_row(r2).unwrap();
        assert!(r2_resolved.has(&Label::new("x")));
        assert!(r2_resolved.is_open());

        // Both tails should be the same fresh variable.
        assert_eq!(r1_resolved.rest, r2_resolved.rest);

        // The fresh variable should lack both x and y.
        let r3 = r1_resolved.rest.unwrap();
        assert!(u.lacks.lacks(r3, &Label::new("x")));
        assert!(u.lacks.lacks(r3, &Label::new("y")));
    }

    #[test]
    fn remy_decomposition_common_fields() {
        let mut u = Unifier::new();
        let r1 = RowVarId(100);
        let r2 = RowVarId(101);

        // {x: Int, z: Bool | r1} unified with {y: String, z: Bool | r2}
        let row1 = RowType::open(
            vec![(Label::new("x"), Type::Int), (Label::new("z"), Type::Bool)],
            r1,
        );
        let row2 = RowType::open(
            vec![
                (Label::new("y"), Type::String),
                (Label::new("z"), Type::Bool),
            ],
            r2,
        );
        u.unify_rows(&row1, &row2, &test_prov());
        assert!(!u.has_errors());

        // r1 bound to {y: String | r3}
        let r1_resolved = u.substitution.lookup_row(r1).unwrap();
        assert!(r1_resolved.has(&Label::new("y")));

        // r2 bound to {x: Int | r3}
        let r2_resolved = u.substitution.lookup_row(r2).unwrap();
        assert!(r2_resolved.has(&Label::new("x")));
    }

    #[test]
    fn remy_with_preexisting_lacks_on_both_sides() {
        // This tests the ordering bug: lacks checks must happen BEFORE transfer.
        // r1 lacks "y", r2 lacks "x". Unifying {x: Int | r1} with {y: Bool | r2}
        // should fail because:
        //   r1 → {y: Bool | r3} but r1 already lacks "y"
        //   r2 → {x: Int | r3} but r2 already lacks "x"
        let mut u = Unifier::new();
        let r1 = RowVarId(100);
        let r2 = RowVarId(101);

        // Pre-existing lacks: r1 lacks "y", r2 lacks "x"
        u.lacks.add(r1, Label::new("y"));
        u.lacks.add(r2, Label::new("x"));

        let row1 = RowType::open(vec![(Label::new("x"), Type::Int)], r1);
        let row2 = RowType::open(vec![(Label::new("y"), Type::Bool)], r2);
        u.unify_rows(&row1, &row2, &test_prov());

        // Both sides should produce duplicate field errors.
        assert!(u.has_errors());
        assert_eq!(
            u.errors().len(),
            2,
            "expected 2 duplicate field errors, got: {:?}",
            u.errors()
        );
        assert!(
            u.errors()
                .iter()
                .all(|e| e.message.contains("cannot add field"))
        );
    }

    #[test]
    fn remy_with_preexisting_lacks_one_side() {
        // r1 lacks "y" but r2 does NOT lack "x". Unifying {x: Int | r1} with {y: Bool | r2}
        // should fail for r1 (can't accept "y") but succeed for r2 (can accept "x").
        let mut u = Unifier::new();
        let r1 = RowVarId(100);
        let r2 = RowVarId(101);

        u.lacks.add(r1, Label::new("y"));

        let row1 = RowType::open(vec![(Label::new("x"), Type::Int)], r1);
        let row2 = RowType::open(vec![(Label::new("y"), Type::Bool)], r2);
        u.unify_rows(&row1, &row2, &test_prov());

        assert!(u.has_errors());
        assert_eq!(u.errors().len(), 1);
        assert!(
            u.errors()[0].message.contains("cannot add field `y`"),
            "got: {}",
            u.errors()[0].message
        );
    }

    #[test]
    fn remy_no_preexisting_lacks_succeeds() {
        // Sanity: with no pre-existing lacks, Rémy decomposition should succeed.
        let mut u = Unifier::new();
        let r1 = RowVarId(100);
        let r2 = RowVarId(101);

        let row1 = RowType::open(vec![(Label::new("x"), Type::Int)], r1);
        let row2 = RowType::open(vec![(Label::new("y"), Type::Bool)], r2);
        u.unify_rows(&row1, &row2, &test_prov());
        assert!(!u.has_errors());
    }

    #[test]
    fn constraint_solver_basic() {
        let mut ctx = InferenceContext::new();
        let a = ctx.fresh_type();
        ctx.constrain_equal(
            a.clone(),
            Type::Int,
            Provenance {
                span: test_span(),
                reason: Reason::LetAnnotation,
            },
        );

        let result = ctx.solve();
        assert!(result.is_ok());
        // Variable generated during constraint collection is resolved by the same unifier.
        assert_eq!(ctx.substitution().apply(&a), Type::Int);
    }

    #[test]
    fn unifier_constraint_capture_logs_constraints() {
        let mut u = Unifier::new();
        u.enable_constraint_capture();
        u.constrain(Constraint::TypeEqual {
            expected: Type::Int,
            actual: Type::Int,
            provenance: test_prov(),
        });

        let captured = u.take_captured_constraints();
        assert_eq!(captured.len(), 1);
        assert!(matches!(captured[0], Constraint::TypeEqual { .. }));

        // Taking again should drain the buffer.
        assert!(u.take_captured_constraints().is_empty());
    }

    #[test]
    fn constraint_scope_discard_drops_local_constraints() {
        let mut ctx = InferenceContext::new();
        let a = ctx.fresh_type();
        ctx.push_constraint_scope();
        ctx.constrain_equal(a.clone(), Type::Int, test_prov());
        assert!(ctx.pop_constraint_scope(false));

        let result = ctx.solve();
        assert!(result.is_ok());
        assert_eq!(
            ctx.substitution().apply(&a),
            a,
            "discarded scope must not contribute constraints"
        );
    }

    #[test]
    fn constraint_scope_commit_keeps_local_constraints() {
        let mut ctx = InferenceContext::new();
        let a = ctx.fresh_type();
        ctx.push_constraint_scope();
        ctx.constrain_equal(a.clone(), Type::Int, test_prov());
        assert!(ctx.pop_constraint_scope(true));

        let result = ctx.solve();
        assert!(result.is_ok());
        assert_eq!(ctx.substitution().apply(&a), Type::Int);
    }

    #[test]
    fn constraint_scope_pop_root_returns_false() {
        let mut ctx = InferenceContext::new();
        assert!(
            !ctx.pop_constraint_scope(true),
            "cannot pop root constraint scope"
        );
        assert!(
            !ctx.pop_constraint_scope(false),
            "cannot pop root constraint scope"
        );
    }

    #[test]
    fn unifier_scope_rollback_discards_substitution_keeps_errors_and_fresh_ids() {
        let mut u = Unifier::new();
        let outer = u.fresh_type_var();
        let scope = u.begin_scope();
        let inner = u.fresh_type_var();

        u.constrain(Constraint::TypeEqual {
            expected: Type::Var(inner),
            actual: Type::Int,
            provenance: test_prov(),
        });
        u.constrain(Constraint::TypeEqual {
            expected: Type::Int,
            actual: Type::Bool,
            provenance: test_prov(),
        });

        u.end_scope(scope, false);

        assert_eq!(u.substitution.apply(&Type::Var(inner)), Type::Var(inner));
        assert!(
            u.has_errors(),
            "rollback scope should preserve diagnostics emitted inside branch"
        );

        let after = u.fresh_type_var();
        assert!(
            after.0 > inner.0 && after.0 > outer.0,
            "fresh IDs must remain monotone across rolled-back scopes"
        );
    }

    #[test]
    fn unifier_scope_commit_keeps_branch_state() {
        let mut u = Unifier::new();
        let tv = u.fresh_type_var();
        let scope = u.begin_scope();
        u.constrain(Constraint::TypeEqual {
            expected: Type::Var(tv),
            actual: Type::Int,
            provenance: test_prov(),
        });
        u.end_scope(scope, true);
        assert_eq!(u.substitution.apply(&Type::Var(tv)), Type::Int);
    }

    #[test]
    fn kind_constraint_reports_mismatch() {
        let mut u = Unifier::new();
        let constraints = vec![Constraint::KindEqual {
            expected: Kind::Star,
            actual: Kind::Eff,
            provenance: test_prov(),
        }];
        let err = u
            .solve(constraints)
            .expect_err("kind mismatch should fail solving");
        assert!(
            err.to_string().contains("kind mismatch"),
            "expected kind mismatch diagnostic, got: {err}"
        );
    }

    #[test]
    fn pending_trait_obligation_is_checked_after_solving() {
        let mut u = Unifier::new();
        u.constrain(Constraint::TraitObligation {
            ty: Type::Int,
            trait_name: "MissingTrait".to_string(),
            provenance: test_prov(),
        });
        let traits = crate::typeck::TraitRegistry::new();
        u.check_trait_bounds(&traits);
        assert!(
            u.has_errors(),
            "missing trait obligation should produce an error"
        );
    }

    #[test]
    fn trait_bound_error_from_solved_var_keeps_source_location() {
        let mut u = Unifier::new();
        let tv = u.fresh_type_var();
        let span = Span::new(kea_ast::FileId(7), 11, 23);

        u.solve(vec![
            Constraint::TraitObligation {
                ty: Type::Var(tv),
                trait_name: "MissingTrait".to_string(),
                provenance: Provenance {
                    span,
                    reason: Reason::TraitBound {
                        trait_name: "MissingTrait".to_string(),
                    },
                },
            },
            Constraint::TypeEqual {
                expected: Type::Var(tv),
                actual: Type::Int,
                provenance: test_prov(),
            },
        ])
        .expect("type constraints should solve before trait bound checking");

        let traits = crate::typeck::TraitRegistry::new();
        u.check_trait_bounds(&traits);
        assert!(u.has_errors(), "expected missing trait-bound error");
        let loc = u
            .errors()
            .iter()
            .find(|d| {
                d.message
                    .contains("does not implement trait `MissingTrait`")
            })
            .and_then(|d| d.location);
        assert_eq!(
            loc,
            Some(SourceLocation {
                file_id: 7,
                start: 11,
                end: 23,
            }),
            "trait-bound diagnostic should keep call-site location"
        );
    }

    #[test]
    fn pending_assoc_projection_obligation_is_checked_after_solving() {
        let mut u = Unifier::new();
        u.constrain(Constraint::AssocTypeEqual {
            base_trait: "MissingTrait".to_string(),
            base_ty: Type::Int,
            assoc: "Item".to_string(),
            rhs: Type::Int,
            provenance: test_prov(),
        });
        let traits = crate::typeck::TraitRegistry::new();
        u.check_trait_bounds(&traits);
        assert!(
            u.has_errors(),
            "missing projection obligation should produce an error"
        );
    }

    #[test]
    fn solver_budget_reports_overflow_with_recent_constraints() {
        let mut u = Unifier::new();
        let constraints = vec![
            Constraint::TypeEqual {
                expected: Type::Int,
                actual: Type::Int,
                provenance: test_prov(),
            },
            Constraint::TypeEqual {
                expected: Type::Bool,
                actual: Type::Bool,
                provenance: test_prov(),
            },
        ];

        let msg = u
            .solve_with_budget_for_test(constraints, 1)
            .expect_err("expected budget error")
            .to_string();
        assert!(
            msg.contains("constraint solver exceeded iteration budget"),
            "diagnostic should explain overflow: {msg}"
        );
        assert!(
            msg.contains("recent constraints:"),
            "diagnostic should include recent constraint trace: {msg}"
        );
    }

    #[test]
    fn solver_is_idempotent_on_solved_constraints() {
        let mut u = Unifier::new();
        let v0 = Type::Var(TypeVarId(0));
        let v1 = Type::Var(TypeVarId(1));
        let constraints = vec![
            Constraint::TypeEqual {
                expected: v0.clone(),
                actual: Type::Int,
                provenance: test_prov(),
            },
            Constraint::TypeEqual {
                expected: v1.clone(),
                actual: v0.clone(),
                provenance: test_prov(),
            },
        ];

        let first = u.solve(constraints.clone());
        assert!(first.is_ok());
        let after_first_v0 = u.substitution.apply(&v0);
        let after_first_v1 = u.substitution.apply(&v1);

        let second = u.solve(constraints);
        assert!(second.is_ok());
        assert_eq!(u.substitution.apply(&v0), after_first_v0);
        assert_eq!(u.substitution.apply(&v1), after_first_v1);
    }

    #[test]
    fn inference_context_shared_counters() {
        // Verify that InferenceContext and its Unifier share variable counters.
        // Fresh vars from ctx should not collide with vars generated during solving.
        let mut ctx = InferenceContext::with_var_offsets(0, 0, 0);

        // Generate some variables through the context.
        let a = ctx.fresh_type_var();
        let b = ctx.fresh_type_var();
        let r = ctx.fresh_row_var();
        let d = ctx.fresh_dim_var();

        // These should be sequential.
        assert_eq!(a, TypeVarId(0));
        assert_eq!(b, TypeVarId(1));
        assert_eq!(r, RowVarId(0));
        assert_eq!(d, DimVarId(0));

        // Variables generated by the unifier during solving continue the sequence.
        let c = ctx.unifier_mut().fresh_type_var();
        assert_eq!(c, TypeVarId(2));
        let d2 = ctx.unifier_mut().fresh_dim_var();
        assert_eq!(d2, DimVarId(1));
    }
}
