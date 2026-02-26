//! Tracing types for compiler observability.
//!
//! These types capture step-by-step traces of unification and type inference,
//! enabling MCP tools to expose the compiler's reasoning process.
//! All tracing is opt-in via `Unifier::enable_tracing()` — zero overhead
//! when disabled.

use serde::Serialize;

// ---------------------------------------------------------------------------
// Unification trace
// ---------------------------------------------------------------------------

/// A single step in a unification trace.
#[derive(Debug, Clone, Serialize)]
pub struct UnifyStep {
    pub step: usize,
    pub action: UnifyAction,
    pub left: String,
    pub right: String,
    pub detail: String,
}

/// What action was taken during a unification step.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum UnifyAction {
    /// Types are already identical — no-op.
    Identity,
    /// Structural recursion: decompose compound types (e.g. List(A) ~ List(B) → A ~ B).
    Decompose,
    /// Type variable bound to a concrete type (e.g. t0 := Int).
    Bind,
    /// Entered row unification.
    UnifyRows,
    /// Row variable bound to residual fields (e.g. r0 := { city: String }).
    BindRowVar,
    /// Rémy-style decomposition: both rows open, fresh tail variable created.
    RemyDecompose,
    /// Occurs check fired — infinite type prevented.
    OccursCheck,
    /// Unification failed — type mismatch.
    Error,
}

// ---------------------------------------------------------------------------
// Inference trace
// ---------------------------------------------------------------------------

/// A single step in an inference trace.
#[derive(Debug, Clone, Serialize)]
pub struct InferStep {
    pub expr: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub rule: InferRule,
    pub detail: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<(usize, usize)>,
}

/// Which inference rule fired.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum InferRule {
    Literal,
    VarLookup,
    Lambda,
    Call,
    Let,
    LetGen,
    If,
    Case,
    BinaryOp,
    Record,
    AnonRecord,
    List,
    Tuple,
    FieldAccess,
    Try,
    Instantiate,
}

// ---------------------------------------------------------------------------
// Trait provenance
// ---------------------------------------------------------------------------

/// Provenance analysis for a single (type, trait) pair.
///
/// Answers "why does/doesn't type T implement trait X?" with full
/// derivation chain: impl source, supertrait satisfaction, per-field
/// derivability, and coherence information.
#[derive(Debug, Clone, Serialize)]
pub struct TraitProvenance {
    pub status: TraitStatus,
    /// If implemented, how: "builtin", "manual", "derive", or "conditional".
    #[serde(skip_serializing_if = "Option::is_none")]
    pub impl_source: Option<String>,
    /// Supertrait chain: each supertrait and whether it's satisfied.
    pub supertraits: Vec<SupertraitStatus>,
    /// Field-level derivability analysis (present for records and sum types).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub derive_analysis: Option<DeriveAnalysis>,
    /// Coherence information (orphan rule, existing impls).
    pub coherence: CoherenceInfo,
    /// Actionable suggestion for the agent.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggestion: Option<String>,
}

/// Overall status of trait resolution.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TraitStatus {
    /// Type implements the trait.
    Implemented,
    /// Type does not implement the trait but could via `deriving ...`.
    Derivable,
    /// Type does not implement the trait; derive would fail on some fields.
    NotDerivable,
    /// Type does not implement the trait; not a record/sum, so manual impl required.
    ManualImplRequired,
    /// The trait does not exist.
    UnknownTrait,
}

/// Status of a single supertrait in the resolution chain.
#[derive(Debug, Clone, Serialize)]
pub struct SupertraitStatus {
    pub trait_name: String,
    pub satisfied: bool,
    /// If satisfied, how: "builtin", "manual", "derive", "conditional".
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
}

/// Field-level analysis of whether a type can derive a trait.
#[derive(Debug, Clone, Serialize)]
pub struct DeriveAnalysis {
    pub can_derive: bool,
    pub fields: Vec<FieldTraitStatus>,
    /// Names of fields that block derivation.
    pub blocking: Vec<String>,
}

/// Whether a single field's type supports a trait.
#[derive(Debug, Clone, Serialize)]
pub struct FieldTraitStatus {
    pub name: String,
    /// Display form of the field type.
    #[serde(rename = "type")]
    pub ty: String,
    pub ok: bool,
    /// If ok, how the field type supports the trait.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    /// If not ok, why the field type doesn't support the trait.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

/// Coherence information for a potential trait impl.
#[derive(Debug, Clone, Serialize)]
pub struct CoherenceInfo {
    /// Whether the orphan rule allows adding an impl here.
    pub orphan_ok: bool,
    /// Existing impls for this (trait, type) pair.
    pub existing_impls: Vec<String>,
    /// If orphan_ok is false, the reason.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub orphan_reason: Option<String>,
}
