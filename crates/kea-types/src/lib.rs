//! Type representations for Kea.
//!
//! This crate defines the semantic types used by the type checker and
//! inference engine. These are distinct from syntactic type annotations
//! (which live in `kea-ast`).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

// ---------------------------------------------------------------------------
// Identifiers
// ---------------------------------------------------------------------------

/// Unique identifier for a type variable during inference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVarId(pub u32);

/// Unique identifier for a row variable during inference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RowVarId(pub u32);

/// Unique identifier for an integer-level inference variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DimVarId(pub u32);

/// A compile-time integer parameter.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Dim {
    /// Concrete known integer value.
    Known(i64),
    /// Inference variable resolved by the solver.
    Var(DimVarId),
}

impl fmt::Display for Dim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Dim::Known(value) => write!(f, "{value}"),
            Dim::Var(var) => write!(f, "d{}", var.0),
        }
    }
}

/// Bit-width for precision integer types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntWidth {
    I8,
    I16,
    I32,
    I64,
}

/// Signedness marker for precision integer types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Signedness {
    Signed,
    Unsigned,
}

/// Bit-width for precision floating-point types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FloatWidth {
    F16,
    F32,
    F64,
}

/// A field/column label. Uses String for now; can switch to interned strings later.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Label(pub String);

impl Label {
    pub fn new(s: impl Into<String>) -> Self {
        Self(s.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// ---------------------------------------------------------------------------
// Kinds
// ---------------------------------------------------------------------------

/// Kind of a type or type constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    Star,
    Eff,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::Star => write!(f, "*"),
            Kind::Eff => write!(f, "Eff"),
        }
    }
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A semantic type in Kea.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    // -- Primitives --
    Int,
    /// Precision integer (e.g. Int32, UInt8).
    IntN(IntWidth, Signedness),
    Float,
    /// Precision floating point (e.g. Float16, Float32).
    FloatN(FloatWidth),
    /// Fixed-point decimal with precision and scale (e.g. Decimal(18, 2)).
    Decimal {
        precision: Dim,
        scale: Dim,
    },
    Bool,
    String,
    Html,
    Markdown,
    Unit,
    Never,
    /// Atom: a compile-time symbol (e.g., `:restart`, `:one_for_one`).
    Atom,
    /// Calendar date (days since Unix epoch, Arrow Date32).
    Date,
    /// UTC timestamp (microseconds since Unix epoch, Arrow Timestamp(Microsecond, UTC)).
    DateTime,
    /// Dynamically typed value placeholder.
    Dynamic,

    // -- Compound types --
    List(Box<Type>),
    /// Arrow-compatible fixed-size list: `FixedSizeList(T, N)`.
    FixedSizeList {
        element: Box<Type>,
        size: Dim,
    },
    /// Tensor with compile-time shape dimensions.
    Tensor {
        element: Box<Type>,
        shape: Vec<Dim>,
    },
    Map(Box<Type>, Box<Type>),
    Set(Box<Type>),
    Tuple(Vec<Type>),
    Option(Box<Type>),
    Result(Box<Type>, Box<Type>),
    /// Existential capability type: `any Show`, `any (Show, Eq)`.
    Existential {
        bounds: Vec<String>,
        associated_types: BTreeMap<String, Type>,
    },

    // -- Records --
    /// Nominal record: `record User { name: String }`.
    /// The name identifies the type for trait dispatch; the row describes fields.
    Record(RecordType),
    /// Anonymous/structural record: `#{ name: "x" }`.
    AnonRecord(RowType),

    // -- Sum types --
    /// Nominal sum type: `type Color = Red | Green | Blue`.
    Sum(SumType),
    /// Nominal opaque type: `opaque UserId = Int`.
    Opaque {
        name: String,
        params: Vec<Type>,
    },

    /// Type with compile-time metadata tags (e.g., future dimensional analysis).
    /// Tags are erased at runtime.
    Tagged {
        inner: Box<Type>,
        tags: BTreeMap<String, i64>,
    },
    /// Lazy typed stream of values.
    Stream(Box<Type>),
    /// Handle to a spawned task yielding `T`.
    Task(Box<Type>),

    // -- Actor (Phase 4, defined now for extensibility) --
    /// Handle to a spawned actor with state type `T`.
    Actor(Box<Type>),

    // -- Shared reference --
    /// `Arc(T)` — the only user-visible shared reference type (KERNEL §1.2).
    Arc(Box<Type>),

    // -- Functions --
    Function(FunctionType),
    /// Explicitly quantified polymorphic type used in nested positions
    /// (for example rank-2 function parameters).
    Forall(Box<TypeScheme>),

    // -- Inference variables --
    /// Unresolved type variable. Never appears in final types.
    Var(TypeVarId),
    /// Type constructor application: `F(A, ...)`.
    ///
    /// Internal representation used for constructor-variable inference.
    App(Box<Type>, Vec<Type>),
    /// Internal partially-applied constructor placeholder.
    ///
    /// `fixed_args` stores concrete argument positions; missing positions are
    /// holes to be filled left-to-right when applied.
    Constructor {
        name: String,
        fixed_args: Vec<(usize, Type)>,
        arity: usize,
    },

    // -- Row as a type (for row-polymorphic positions) --
    Row(RowType),
}

pub const BUILTIN_ERROR_TYPE_NAMES: [&str; 4] =
    ["IOError", "SchemaError", "ExecError", "ActorError"];
pub const BUILTIN_PROTOCOL_TYPE_NAMES: [&str; 3] =
    ["SupervisionAction", "SupervisorStrategy", "ActorSignal"];

pub fn is_builtin_error_type_name(name: &str) -> bool {
    matches!(name, "IOError" | "SchemaError" | "ExecError" | "ActorError")
}

/// Build the canonical builtin error sum type.
///
/// Most builtin errors are single-variant: `type IOError = IOError(String)`.
/// `ActorError` is multi-variant: `type ActorError = Dead(String) | MailboxFull(String) | Timeout(String) | Custom(String)`.
pub fn builtin_error_sum_type(name: &str) -> Option<Type> {
    if !is_builtin_error_type_name(name) {
        return None;
    }
    if name == "ActorError" {
        return Some(Type::Sum(SumType {
            name: "ActorError".to_string(),
            type_args: vec![],
            variants: vec![
                ("Dead".to_string(), vec![Type::String]),
                ("MailboxFull".to_string(), vec![Type::String]),
                ("Timeout".to_string(), vec![Type::String]),
                ("Custom".to_string(), vec![Type::String]),
            ],
        }));
    }
    Some(Type::Sum(SumType {
        name: name.to_string(),
        type_args: vec![],
        variants: vec![(name.to_string(), vec![Type::String])],
    }))
}

pub fn is_builtin_protocol_type_name(name: &str) -> bool {
    matches!(
        name,
        "SupervisionAction" | "SupervisorStrategy" | "ActorSignal"
    )
}

pub fn builtin_protocol_sum_type(name: &str) -> Option<Type> {
    if !is_builtin_protocol_type_name(name) {
        return None;
    }
    let variants = match name {
        "SupervisionAction" => vec![
            ("Restart".to_string(), vec![]),
            ("Stop".to_string(), vec![]),
            ("Escalate".to_string(), vec![]),
        ],
        "SupervisorStrategy" => vec![
            ("OneForOne".to_string(), vec![]),
            ("OneForAll".to_string(), vec![]),
            ("RestForOne".to_string(), vec![]),
        ],
        "ActorSignal" => vec![
            ("Shutdown".to_string(), vec![]),
            ("Kill".to_string(), vec![]),
        ],
        _ => return None,
    };
    Some(Type::Sum(SumType {
        name: name.to_string(),
        type_args: vec![],
        variants,
    }))
}

pub fn builtin_sum_type(name: &str) -> Option<Type> {
    builtin_error_sum_type(name).or_else(|| builtin_protocol_sum_type(name))
}

/// Function type: `(params) -[effects]> ret`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub params: Vec<Type>,
    pub ret: Box<Type>,
    pub effects: EffectRow,
}

impl FunctionType {
    pub fn pure(params: Vec<Type>, ret: Type) -> Self {
        Self {
            params,
            ret: Box::new(ret),
            effects: EffectRow::pure(),
        }
    }

    pub fn with_effects(params: Vec<Type>, ret: Type, effects: EffectRow) -> Self {
        Self {
            params,
            ret: Box::new(ret),
            effects,
        }
    }
}

/// A nominal record type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordType {
    pub name: String,
    pub params: Vec<Type>,
    pub row: RowType,
}

/// A nominal sum type (algebraic data type).
///
/// Each variant has a name and zero or more positional field types.
/// Example: `type Shape = Circle(Float) | Rectangle(Float, Float)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumType {
    pub name: String,
    /// Instantiated type arguments for this nominal sum type.
    pub type_args: Vec<Type>,
    pub variants: Vec<(String, Vec<Type>)>,
}

// ---------------------------------------------------------------------------
// Row types
// ---------------------------------------------------------------------------

/// A row type represents an unordered set of label-type pairs, either open or closed.
///
/// - Closed: `fields` contains all labels, `rest` is `None`.
/// - Open: `fields` contains known labels, `rest` is `Some(var)` for the unknown tail.
///
/// Fields are kept sorted by label for canonical representation.
/// This is critical for deterministic unification (KERNEL §2.2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RowType {
    /// Known fields, sorted by label.
    pub fields: Vec<(Label, Type)>,
    /// `None` = closed row. `Some(var)` = open row with tail variable.
    pub rest: Option<RowVarId>,
}

impl RowType {
    /// Create a closed row with the given fields. Sorts by label.
    pub fn closed(mut fields: Vec<(Label, Type)>) -> Self {
        fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        Self { fields, rest: None }
    }

    /// Create an open row with the given fields and a tail variable. Sorts by label.
    pub fn open(mut fields: Vec<(Label, Type)>, rest: RowVarId) -> Self {
        fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        Self {
            fields,
            rest: Some(rest),
        }
    }

    /// Create an empty open row (just a row variable).
    pub fn empty_open(rest: RowVarId) -> Self {
        Self {
            fields: Vec::new(),
            rest: Some(rest),
        }
    }

    /// Create an empty closed row.
    pub fn empty_closed() -> Self {
        Self {
            fields: Vec::new(),
            rest: None,
        }
    }

    pub fn is_closed(&self) -> bool {
        self.rest.is_none()
    }

    pub fn is_open(&self) -> bool {
        self.rest.is_some()
    }

    /// Look up a field by label.
    pub fn get(&self, label: &Label) -> Option<&Type> {
        self.fields
            .binary_search_by(|(l, _)| l.cmp(label))
            .ok()
            .map(|idx| &self.fields[idx].1)
    }

    /// Check whether this row contains a label.
    pub fn has(&self, label: &Label) -> bool {
        self.fields.binary_search_by(|(l, _)| l.cmp(label)).is_ok()
    }

    /// Labels in this row.
    pub fn labels(&self) -> impl Iterator<Item = &Label> {
        self.fields.iter().map(|(l, _)| l)
    }
}

/// Effect row representation.
///
/// Effect rows reuse the same Rémy row machinery as record rows:
/// the payload type is the field type and the open-tail variable is shared.
/// Convention: effects without payload use `Type::Unit`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectRow {
    pub row: RowType,
}

impl EffectRow {
    /// Closed empty effect row (`[]`).
    pub fn pure() -> Self {
        Self {
            row: RowType::empty_closed(),
        }
    }

    /// Closed effect row.
    pub fn closed(effects: Vec<(Label, Type)>) -> Self {
        Self {
            row: RowType::closed(effects),
        }
    }

    /// Open effect row with a tail variable.
    pub fn open(effects: Vec<(Label, Type)>, rest: RowVarId) -> Self {
        Self {
            row: RowType::open(effects, rest),
        }
    }

    pub fn is_pure(&self) -> bool {
        self.row.fields.is_empty() && self.row.rest.is_none()
    }

    pub fn as_row(&self) -> &RowType {
        &self.row
    }

    pub fn into_row(self) -> RowType {
        self.row
    }
}

impl fmt::Display for EffectRow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, (label, payload)) in self.row.fields.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            if matches!(payload, Type::Unit) {
                write!(f, "{label}")?;
            } else {
                write!(f, "{label}({payload})")?;
            }
        }
        if let Some(rest) = self.row.rest {
            if !self.row.fields.is_empty() {
                write!(f, " | ")?;
            }
            write!(f, "e{}", rest.0)?;
        }
        write!(f, "]")
    }
}

/// Handler contract for `handle` expressions.
///
/// `handled` is the effect row this handler discharges.
/// `input` and `output` are value-level domain/codomain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HandlerType {
    pub handled: EffectRow,
    pub input: Box<Type>,
    pub output: Box<Type>,
}

impl fmt::Display for HandlerType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "handler {} -{}> {}",
            self.input, self.handled, self.output
        )
    }
}

// ---------------------------------------------------------------------------
// Display for Type (user-facing Kea syntax)
// ---------------------------------------------------------------------------

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::IntN(width, Signedness::Signed) => match width {
                IntWidth::I8 => write!(f, "Int8"),
                IntWidth::I16 => write!(f, "Int16"),
                IntWidth::I32 => write!(f, "Int32"),
                IntWidth::I64 => write!(f, "Int64"),
            },
            Type::IntN(width, Signedness::Unsigned) => match width {
                IntWidth::I8 => write!(f, "UInt8"),
                IntWidth::I16 => write!(f, "UInt16"),
                IntWidth::I32 => write!(f, "UInt32"),
                IntWidth::I64 => write!(f, "UInt64"),
            },
            Type::Float => write!(f, "Float"),
            Type::FloatN(width) => match width {
                FloatWidth::F16 => write!(f, "Float16"),
                FloatWidth::F32 => write!(f, "Float32"),
                FloatWidth::F64 => write!(f, "Float64"),
            },
            Type::Decimal { precision, scale } => write!(f, "Decimal({precision}, {scale})"),
            Type::Bool => write!(f, "Bool"),
            Type::String => write!(f, "String"),
            Type::Html => write!(f, "Html"),
            Type::Markdown => write!(f, "Markdown"),
            Type::Unit => write!(f, "()"),
            Type::Never => write!(f, "Never"),
            Type::Atom => write!(f, "Atom"),
            Type::Date => write!(f, "Date"),
            Type::DateTime => write!(f, "DateTime"),
            Type::Dynamic => write!(f, "Dynamic"),

            Type::List(inner) => write!(f, "List({inner})"),
            Type::FixedSizeList { element, size } => {
                write!(f, "FixedSizeList({element}, {size})")
            }
            Type::Tensor { element, shape } => {
                write!(f, "Tensor({element}, [")?;
                for (idx, dim) in shape.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{dim}")?;
                }
                write!(f, "])")
            }
            Type::Map(k, v) => write!(f, "Map({k}, {v})"),
            Type::Set(inner) => write!(f, "Set({inner})"),

            Type::Tuple(elems) => {
                write!(f, "#(")?;
                for (i, t) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{t}")?;
                }
                write!(f, ")")
            }

            Type::Option(inner) => write!(f, "{inner}?"),
            Type::Result(ok, err) => write!(f, "Result({ok}, {err})"),
            Type::Existential {
                bounds,
                associated_types,
            } => {
                write!(f, "any ")?;
                if bounds.len() == 1 {
                    write!(f, "{}", bounds[0])?;
                } else {
                    write!(f, "(")?;
                    for (i, b) in bounds.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{b}")?;
                    }
                    write!(f, ")")?;
                }
                if !associated_types.is_empty() {
                    write!(f, " where ")?;
                    for (i, (name, ty)) in associated_types.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{name} = {ty}")?;
                    }
                }
                Ok(())
            }

            Type::Record(rt) => {
                write!(f, "{}", rt.name)?;
                if !rt.params.is_empty() {
                    write!(f, "(")?;
                    for (i, p) in rt.params.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{p}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::AnonRecord(row) => {
                write!(f, "#{{ ")?;
                write_row_fields(f, row)?;
                write!(f, " }}")
            }
            Type::Sum(st) => {
                write!(f, "{}", st.name)?;
                if !st.type_args.is_empty() {
                    write!(f, "(")?;
                    for (i, p) in st.type_args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{p}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::Opaque { name, params } => {
                write!(f, "{name}")?;
                if !params.is_empty() {
                    write!(f, "(")?;
                    for (i, p) in params.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{p}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }

            Type::Tagged { inner, tags } => {
                if tags.is_empty() {
                    write!(f, "Tagged({inner})")
                } else {
                    write!(f, "{inner} :: {{")?;
                    for (i, (k, v)) in tags.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{k}: {v}")?;
                    }
                    write!(f, "}}")
                }
            }
            Type::Stream(inner) => write!(f, "Stream({inner})"),
            Type::Task(inner) => write!(f, "Task({inner})"),

            Type::Actor(inner) => write!(f, "Actor({inner})"),
            Type::Arc(inner) => write!(f, "Arc({inner})"),

            Type::Function(ft) => {
                write!(f, "(")?;
                for (i, p) in ft.params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{p}")?;
                }
                if ft.effects.is_pure() {
                    write!(f, ") -> {}", ft.ret)
                } else {
                    write!(f, ") -{}> {}", ft.effects, ft.ret)
                }
            }
            Type::Forall(scheme) => {
                let names: Vec<String> = scheme
                    .type_vars
                    .iter()
                    .enumerate()
                    .map(|(i, _)| alphabetic_var_name(i))
                    .collect();
                let type_mapping: BTreeMap<TypeVarId, String> = scheme
                    .type_vars
                    .iter()
                    .copied()
                    .zip(names.iter().cloned())
                    .collect();
                let row_mapping: BTreeMap<RowVarId, String> = scheme
                    .row_vars
                    .iter()
                    .enumerate()
                    .map(|(i, rv)| (*rv, format!("r{}", alphabetic_var_name(i))))
                    .collect();
                let dim_mapping: BTreeMap<DimVarId, String> = scheme
                    .dim_vars
                    .iter()
                    .enumerate()
                    .map(|(i, dv)| (*dv, format!("d{}", alphabetic_var_name(i))))
                    .collect();
                write!(
                    f,
                    "forall {}. {}",
                    names.join(", "),
                    sanitize_type_display_with_mappings(
                        &scheme.ty,
                        &type_mapping,
                        &row_mapping,
                        &dim_mapping
                    )
                )
            }

            Type::Var(id) => write!(f, "t{}", id.0),
            Type::App(constructor, args) => {
                write!(f, "{}(", constructor)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            Type::Constructor {
                name,
                fixed_args,
                arity,
            } => {
                write!(f, "<ctor {name}/{arity}")?;
                if !fixed_args.is_empty() {
                    write!(f, " [")?;
                    for (i, (idx, ty)) in fixed_args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{idx}={ty}")?;
                    }
                    write!(f, "]")?;
                }
                write!(f, ">")
            }

            Type::Row(row) => {
                write!(f, "(")?;
                write_row_fields(f, row)?;
                write!(f, ")")
            }
        }
    }
}

fn write_row_fields(f: &mut fmt::Formatter<'_>, row: &RowType) -> fmt::Result {
    for (i, (label, ty)) in row.fields.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{label}: {ty}")?;
    }
    if let Some(rest) = row.rest {
        if !row.fields.is_empty() {
            write!(f, " | ")?;
        }
        write!(f, "r{}", rest.0)?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Type schemes (forall-quantified types)
// ---------------------------------------------------------------------------

/// A type scheme: `forall a b r. T` where `a`, `b` are type vars, `r` are row vars.
///
/// Type schemes arise from let-generalization. A polymorphic binding like
/// `let id = |x| x` gets the scheme `forall a. a -> a`. Each use of `id`
/// instantiates the scheme with fresh variables.
///
/// Lacks constraints on quantified row vars are preserved so they transfer
/// to fresh variables during instantiation (KERNEL §2.2).
///
/// Trait bounds on quantified type vars record where-clause constraints
/// (e.g., `where x: Additive`). These transfer to fresh variables during
/// instantiation and are checked when the variables resolve to concrete types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeScheme {
    pub type_vars: Vec<TypeVarId>,
    pub row_vars: Vec<RowVarId>,
    /// Quantified dimension variables (integer-level inference vars).
    pub dim_vars: Vec<DimVarId>,
    /// Lacks constraints on the quantified row vars.
    pub lacks: BTreeMap<RowVarId, BTreeSet<Label>>,
    /// Trait bounds on the quantified type vars (e.g., `T: Additive`).
    pub bounds: BTreeMap<TypeVarId, BTreeSet<String>>,
    /// Kind assignments for quantified type variables.
    ///
    /// Variables omitted from this map default to kind `*`.
    pub kinds: BTreeMap<TypeVarId, Kind>,
    pub ty: Type,
}

impl TypeScheme {
    /// Create a monomorphic scheme (no quantified variables).
    pub fn mono(ty: Type) -> Self {
        Self {
            type_vars: Vec::new(),
            row_vars: Vec::new(),
            dim_vars: Vec::new(),
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: BTreeMap::new(),
            ty,
        }
    }

    /// Is this scheme monomorphic (no quantified variables)?
    pub fn is_mono(&self) -> bool {
        self.type_vars.is_empty() && self.row_vars.is_empty() && self.dim_vars.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Free variable computation
// ---------------------------------------------------------------------------

/// Collect all free type variables in a type.
pub fn free_type_vars(ty: &Type) -> BTreeSet<TypeVarId> {
    let mut vars = BTreeSet::new();
    collect_free_type_vars(ty, &mut vars);
    vars
}

fn collect_free_type_vars(ty: &Type, vars: &mut BTreeSet<TypeVarId>) {
    match ty {
        Type::Var(v) => {
            vars.insert(*v);
        }
        Type::App(constructor, args) => {
            collect_free_type_vars(constructor, vars);
            for arg in args {
                collect_free_type_vars(arg, vars);
            }
        }
        Type::Constructor { fixed_args, .. } => {
            for (_, ty) in fixed_args {
                collect_free_type_vars(ty, vars);
            }
        }
        Type::List(inner) | Type::Set(inner) | Type::Option(inner) => {
            collect_free_type_vars(inner, vars);
        }
        Type::FixedSizeList { element, .. } | Type::Tensor { element, .. } => {
            collect_free_type_vars(element, vars);
        }
        Type::Map(k, v) | Type::Result(k, v) => {
            collect_free_type_vars(k, vars);
            collect_free_type_vars(v, vars);
        }
        Type::Existential {
            associated_types, ..
        } => {
            for ty in associated_types.values() {
                collect_free_type_vars(ty, vars);
            }
        }
        Type::Tuple(elems) => {
            for t in elems {
                collect_free_type_vars(t, vars);
            }
        }
        Type::Function(ft) => {
            for t in &ft.params {
                collect_free_type_vars(t, vars);
            }
            collect_free_type_vars(&ft.ret, vars);
            collect_free_type_vars_row(&ft.effects.row, vars);
        }
        Type::Forall(scheme) => {
            let mut inner = free_type_vars(&scheme.ty);
            for tv in &scheme.type_vars {
                inner.remove(tv);
            }
            vars.extend(inner);
        }
        Type::Record(rt) => {
            for param in &rt.params {
                collect_free_type_vars(param, vars);
            }
            collect_free_type_vars_row(&rt.row, vars);
        }
        Type::Opaque { params, .. } => {
            for param in params {
                collect_free_type_vars(param, vars);
            }
        }
        Type::AnonRecord(row) | Type::Row(row) => {
            collect_free_type_vars_row(row, vars);
        }
        Type::Sum(st) => {
            for arg in &st.type_args {
                collect_free_type_vars(arg, vars);
            }
            for (_, fields) in &st.variants {
                for t in fields {
                    collect_free_type_vars(t, vars);
                }
            }
        }
        Type::Tagged { inner, .. }
        | Type::Stream(inner)
        | Type::Task(inner)
        | Type::Actor(inner)
        | Type::Arc(inner) => {
            collect_free_type_vars(inner, vars);
        }
        Type::Int
        | Type::IntN(_, _)
        | Type::Float
        | Type::FloatN(_)
        | Type::Decimal { .. }
        | Type::Bool
        | Type::String
        | Type::Html
        | Type::Markdown
        | Type::Unit
        | Type::Never
        | Type::Atom
        | Type::Date
        | Type::DateTime
        | Type::Dynamic => {}
    }
}

fn collect_free_type_vars_row(row: &RowType, vars: &mut BTreeSet<TypeVarId>) {
    for (_, ty) in &row.fields {
        collect_free_type_vars(ty, vars);
    }
}

/// Collect all free row variables in a type.
pub fn free_row_vars(ty: &Type) -> BTreeSet<RowVarId> {
    let mut vars = BTreeSet::new();
    collect_free_row_vars(ty, &mut vars);
    vars
}

fn collect_free_row_vars(ty: &Type, vars: &mut BTreeSet<RowVarId>) {
    match ty {
        Type::Record(rt) => {
            for param in &rt.params {
                collect_free_row_vars(param, vars);
            }
            collect_free_row_vars_row(&rt.row, vars);
        }
        Type::Opaque { params, .. } => {
            for param in params {
                collect_free_row_vars(param, vars);
            }
        }
        Type::AnonRecord(row) | Type::Row(row) => {
            collect_free_row_vars_row(row, vars);
        }
        Type::Sum(st) => {
            for arg in &st.type_args {
                collect_free_row_vars(arg, vars);
            }
            for (_, fields) in &st.variants {
                for t in fields {
                    collect_free_row_vars(t, vars);
                }
            }
        }
        Type::List(inner) | Type::Set(inner) | Type::Option(inner) => {
            collect_free_row_vars(inner, vars);
        }
        Type::FixedSizeList { element, .. } | Type::Tensor { element, .. } => {
            collect_free_row_vars(element, vars);
        }
        Type::Map(k, v) | Type::Result(k, v) => {
            collect_free_row_vars(k, vars);
            collect_free_row_vars(v, vars);
        }
        Type::Existential {
            associated_types, ..
        } => {
            for ty in associated_types.values() {
                collect_free_row_vars(ty, vars);
            }
        }
        Type::Tuple(elems) => {
            for t in elems {
                collect_free_row_vars(t, vars);
            }
        }
        Type::Function(ft) => {
            for t in &ft.params {
                collect_free_row_vars(t, vars);
            }
            collect_free_row_vars(&ft.ret, vars);
            collect_free_row_vars_row(&ft.effects.row, vars);
        }
        Type::Forall(scheme) => {
            let mut inner = free_row_vars(&scheme.ty);
            for rv in &scheme.row_vars {
                inner.remove(rv);
            }
            vars.extend(inner);
        }
        Type::Tagged { inner, .. }
        | Type::Stream(inner)
        | Type::Task(inner)
        | Type::Actor(inner)
        | Type::Arc(inner) => {
            collect_free_row_vars(inner, vars);
        }
        Type::App(constructor, args) => {
            collect_free_row_vars(constructor, vars);
            for arg in args {
                collect_free_row_vars(arg, vars);
            }
        }
        Type::Constructor { fixed_args, .. } => {
            for (_, ty) in fixed_args {
                collect_free_row_vars(ty, vars);
            }
        }
        Type::Var(_)
        | Type::Int
        | Type::IntN(_, _)
        | Type::Float
        | Type::FloatN(_)
        | Type::Decimal { .. }
        | Type::Bool
        | Type::String
        | Type::Html
        | Type::Markdown
        | Type::Unit
        | Type::Never
        | Type::Atom
        | Type::Date
        | Type::DateTime
        | Type::Dynamic => {}
    }
}

fn collect_free_row_vars_row(row: &RowType, vars: &mut BTreeSet<RowVarId>) {
    if let Some(v) = row.rest {
        vars.insert(v);
    }
    for (_, ty) in &row.fields {
        collect_free_row_vars(ty, vars);
    }
}

/// Collect all free dimension variables in a type.
pub fn free_dim_vars(ty: &Type) -> BTreeSet<DimVarId> {
    let mut vars = BTreeSet::new();
    collect_free_dim_vars(ty, &mut vars);
    vars
}

fn collect_free_dim_vars(ty: &Type, vars: &mut BTreeSet<DimVarId>) {
    match ty {
        Type::Record(rt) => {
            for param in &rt.params {
                collect_free_dim_vars(param, vars);
            }
            collect_free_dim_vars_row(&rt.row, vars);
        }
        Type::Opaque { params, .. } => {
            for param in params {
                collect_free_dim_vars(param, vars);
            }
        }
        Type::AnonRecord(row) | Type::Row(row) => {
            collect_free_dim_vars_row(row, vars);
        }
        Type::Sum(st) => {
            for arg in &st.type_args {
                collect_free_dim_vars(arg, vars);
            }
            for (_, fields) in &st.variants {
                for t in fields {
                    collect_free_dim_vars(t, vars);
                }
            }
        }
        Type::List(inner) | Type::Set(inner) | Type::Option(inner) => {
            collect_free_dim_vars(inner, vars);
        }
        Type::FixedSizeList { element, size } => {
            collect_free_dim_vars(element, vars);
            if let Dim::Var(v) = size {
                vars.insert(*v);
            }
        }
        Type::Tensor { element, shape } => {
            collect_free_dim_vars(element, vars);
            for dim in shape {
                if let Dim::Var(v) = dim {
                    vars.insert(*v);
                }
            }
        }
        Type::Map(k, v) | Type::Result(k, v) => {
            collect_free_dim_vars(k, vars);
            collect_free_dim_vars(v, vars);
        }
        Type::Existential {
            associated_types, ..
        } => {
            for ty in associated_types.values() {
                collect_free_dim_vars(ty, vars);
            }
        }
        Type::Tuple(elems) => {
            for t in elems {
                collect_free_dim_vars(t, vars);
            }
        }
        Type::Function(ft) => {
            for t in &ft.params {
                collect_free_dim_vars(t, vars);
            }
            collect_free_dim_vars(&ft.ret, vars);
            collect_free_dim_vars_row(&ft.effects.row, vars);
        }
        Type::Forall(scheme) => {
            let mut inner = free_dim_vars(&scheme.ty);
            for dv in &scheme.dim_vars {
                inner.remove(dv);
            }
            vars.extend(inner);
        }
        Type::Tagged { inner, .. }
        | Type::Stream(inner)
        | Type::Task(inner)
        | Type::Actor(inner)
        | Type::Arc(inner) => {
            collect_free_dim_vars(inner, vars);
        }
        Type::Decimal { precision, scale } => {
            if let Dim::Var(v) = precision {
                vars.insert(*v);
            }
            if let Dim::Var(v) = scale {
                vars.insert(*v);
            }
        }
        Type::App(constructor, args) => {
            collect_free_dim_vars(constructor, vars);
            for arg in args {
                collect_free_dim_vars(arg, vars);
            }
        }
        Type::Constructor { fixed_args, .. } => {
            for (_, ty) in fixed_args {
                collect_free_dim_vars(ty, vars);
            }
        }
        Type::Var(_)
        | Type::Int
        | Type::IntN(_, _)
        | Type::Float
        | Type::FloatN(_)
        | Type::Bool
        | Type::String
        | Type::Html
        | Type::Markdown
        | Type::Unit
        | Type::Never
        | Type::Atom
        | Type::Date
        | Type::DateTime
        | Type::Dynamic => {}
    }
}

fn collect_free_dim_vars_row(row: &RowType, vars: &mut BTreeSet<DimVarId>) {
    for (_, ty) in &row.fields {
        collect_free_dim_vars(ty, vars);
    }
}

// ---------------------------------------------------------------------------
// Type display helpers
// ---------------------------------------------------------------------------

/// Display a type with alphabetic names for type variables instead of `t0`, `t1`.
///
/// Used by MCP and system catalog to present clean, user-facing type strings.
pub fn sanitize_type_display(ty: &Type) -> String {
    let type_vars: Vec<TypeVarId> = free_type_vars(ty).into_iter().collect();
    let row_vars: Vec<RowVarId> = free_row_vars(ty).into_iter().collect();
    let dim_vars: Vec<DimVarId> = free_dim_vars(ty).into_iter().collect();
    if type_vars.is_empty() && row_vars.is_empty() && dim_vars.is_empty() {
        return ty.to_string();
    }
    let type_mapping: BTreeMap<TypeVarId, String> = type_vars
        .iter()
        .enumerate()
        .map(|(i, var)| (*var, alphabetic_var_name(i)))
        .collect();
    let row_mapping: BTreeMap<RowVarId, String> = row_vars
        .iter()
        .enumerate()
        .map(|(i, var)| (*var, format!("r{}", alphabetic_var_name(i))))
        .collect();
    let dim_mapping: BTreeMap<DimVarId, String> = dim_vars
        .iter()
        .enumerate()
        .map(|(i, var)| (*var, format!("d{}", alphabetic_var_name(i))))
        .collect();

    sanitize_type_display_with_mappings(ty, &type_mapping, &row_mapping, &dim_mapping)
}

/// Display two types with one shared variable namespace.
///
/// This keeps mismatch messages consistent: the same source variable appears
/// with the same sanitized name on both sides.
pub fn sanitize_type_pair_display(left: &Type, right: &Type) -> (String, String) {
    let mut type_vars = free_type_vars(left);
    type_vars.extend(free_type_vars(right));

    let mut row_vars = free_row_vars(left);
    row_vars.extend(free_row_vars(right));
    let mut dim_vars = free_dim_vars(left);
    dim_vars.extend(free_dim_vars(right));

    if type_vars.is_empty() && row_vars.is_empty() && dim_vars.is_empty() {
        return (left.to_string(), right.to_string());
    }

    let type_mapping: BTreeMap<TypeVarId, String> = type_vars
        .into_iter()
        .enumerate()
        .map(|(i, var)| (var, alphabetic_var_name(i)))
        .collect();
    let row_mapping: BTreeMap<RowVarId, String> = row_vars
        .into_iter()
        .enumerate()
        .map(|(i, var)| (var, format!("r{}", alphabetic_var_name(i))))
        .collect();
    let dim_mapping: BTreeMap<DimVarId, String> = dim_vars
        .into_iter()
        .enumerate()
        .map(|(i, var)| (var, format!("d{}", alphabetic_var_name(i))))
        .collect();

    (
        sanitize_type_display_with_mappings(left, &type_mapping, &row_mapping, &dim_mapping),
        sanitize_type_display_with_mappings(right, &type_mapping, &row_mapping, &dim_mapping),
    )
}

/// Generate alphabetic variable names: a, b, c, ..., z, a1, b1, ...
fn alphabetic_var_name(index: usize) -> String {
    let letter = (b'a' + (index % 26) as u8) as char;
    let suffix = index / 26;
    if suffix == 0 {
        letter.to_string()
    } else {
        format!("{letter}{suffix}")
    }
}

fn sanitize_type_display_with_mappings(
    ty: &Type,
    type_mapping: &BTreeMap<TypeVarId, String>,
    row_mapping: &BTreeMap<RowVarId, String>,
    dim_mapping: &BTreeMap<DimVarId, String>,
) -> String {
    let mut result = ty.to_string();
    for (var, name) in type_mapping {
        result = replace_var_token(&result, &format!("t{}", var.0), name);
    }
    for (var, name) in row_mapping {
        result = replace_var_token(&result, &format!("r{}", var.0), name);
    }
    for (var, name) in dim_mapping {
        result = replace_var_token(&result, &format!("d{}", var.0), name);
    }
    collapse_decimal_with_dim_vars(&result, dim_mapping)
}

fn collapse_decimal_with_dim_vars(
    rendered: &str,
    dim_mapping: &BTreeMap<DimVarId, String>,
) -> String {
    if dim_mapping.is_empty() {
        return rendered.to_string();
    }
    let dim_names: BTreeSet<&str> = dim_mapping.values().map(String::as_str).collect();
    let mut out = String::with_capacity(rendered.len());
    let mut cursor = 0usize;

    while let Some(found) = rendered[cursor..].find("Decimal(") {
        let start = cursor + found;
        out.push_str(&rendered[cursor..start]);

        let args_start = start + "Decimal(".len();
        let Some(end_rel) = rendered[args_start..].find(')') else {
            out.push_str(&rendered[start..]);
            return out;
        };
        let args_end = args_start + end_rel;
        let args = &rendered[args_start..args_end];

        if let Some((precision, scale)) = args.split_once(',')
            && dim_names.contains(precision.trim())
            && dim_names.contains(scale.trim())
        {
            out.push_str("Decimal");
            cursor = args_end + 1;
            continue;
        }

        out.push_str(&rendered[start..=args_end]);
        cursor = args_end + 1;
    }

    out.push_str(&rendered[cursor..]);
    out
}

fn replace_var_token(input: &str, token: &str, replacement: &str) -> String {
    let mut out = String::with_capacity(input.len());
    let mut idx = 0;

    while idx < input.len() {
        let current = &input[idx..];
        if current.starts_with(token) {
            let prev = if idx == 0 {
                None
            } else {
                input[..idx].chars().next_back()
            };
            let next_idx = idx + token.len();
            let next = if next_idx >= input.len() {
                None
            } else {
                input[next_idx..].chars().next()
            };

            if is_var_token_boundary(prev) && is_var_token_boundary(next) {
                out.push_str(replacement);
                idx = next_idx;
                continue;
            }
        }

        let ch = current
            .chars()
            .next()
            .expect("index is always on a valid char boundary");
        out.push(ch);
        idx += ch.len_utf8();
    }

    out
}

fn is_var_token_boundary(ch: Option<char>) -> bool {
    ch.is_none_or(|c| !(c.is_ascii_alphanumeric() || c == '_'))
}

/// Arity (number of type parameters) for a known builtin type constructor.
pub fn builtin_type_constructor_arity(name: &str) -> Option<usize> {
    Some(match name {
        "Int" | "Int8" | "Int16" | "Int32" | "Int64" | "UInt8" | "UInt16" | "UInt32" | "UInt64"
        | "Float" | "Float16" | "Float32" | "Float64" | "Decimal" | "Bool" | "String" | "Html"
        | "Markdown" | "Unit" | "Atom" | "Date" | "DateTime" | "Dynamic" => 0,
        "List" | "Set" | "Option" | "Stream" | "Task" | "Actor" | "Arc" | "Step" | "Seq" => 1,
        "Map" | "Result" | "Validated" => 2,
        "Tagged" | "Tuple" => return None,
        _ => return None,
    })
}

/// Extract the trait-dispatch type constructor and its type arguments.
///
/// This normalizes built-in constructors (for example `List(Int)` to
/// `("List", [Int])`) so trait lookup can bind impl header type parameters.
pub fn type_constructor_for_trait(ty: &Type) -> Option<(String, Vec<Type>)> {
    match ty {
        Type::Int => Some(("Int".into(), vec![])),
        Type::IntN(IntWidth::I8, Signedness::Signed) => Some(("Int8".into(), vec![])),
        Type::IntN(IntWidth::I16, Signedness::Signed) => Some(("Int16".into(), vec![])),
        Type::IntN(IntWidth::I32, Signedness::Signed) => Some(("Int32".into(), vec![])),
        Type::IntN(IntWidth::I64, Signedness::Signed) => Some(("Int64".into(), vec![])),
        Type::IntN(IntWidth::I8, Signedness::Unsigned) => Some(("UInt8".into(), vec![])),
        Type::IntN(IntWidth::I16, Signedness::Unsigned) => Some(("UInt16".into(), vec![])),
        Type::IntN(IntWidth::I32, Signedness::Unsigned) => Some(("UInt32".into(), vec![])),
        Type::IntN(IntWidth::I64, Signedness::Unsigned) => Some(("UInt64".into(), vec![])),
        Type::Float => Some(("Float".into(), vec![])),
        Type::FloatN(FloatWidth::F16) => Some(("Float16".into(), vec![])),
        Type::FloatN(FloatWidth::F32) => Some(("Float32".into(), vec![])),
        Type::FloatN(FloatWidth::F64) => Some(("Float64".into(), vec![])),
        Type::Decimal { .. } => Some(("Decimal".into(), vec![])),
        Type::Bool => Some(("Bool".into(), vec![])),
        Type::String => Some(("String".into(), vec![])),
        Type::Html => Some(("Html".into(), vec![])),
        Type::Markdown => Some(("Markdown".into(), vec![])),
        Type::Unit => Some(("Unit".into(), vec![])),
        Type::Never => Some(("Never".into(), vec![])),
        Type::Atom => Some(("Atom".into(), vec![])),
        Type::Date => Some(("Date".into(), vec![])),
        Type::DateTime => Some(("DateTime".into(), vec![])),
        Type::Dynamic => Some(("Dynamic".into(), vec![])),
        Type::List(elem) => Some(("List".into(), vec![(**elem).clone()])),
        Type::FixedSizeList { element, .. } => {
            Some(("FixedSizeList".into(), vec![(**element).clone()]))
        }
        Type::Tensor { element, .. } => Some(("Tensor".into(), vec![(**element).clone()])),
        Type::Set(elem) => Some(("Set".into(), vec![(**elem).clone()])),
        Type::Option(inner) => Some(("Option".into(), vec![(**inner).clone()])),
        Type::Map(k, v) => Some(("Map".into(), vec![(**k).clone(), (**v).clone()])),
        Type::Result(ok, err) => Some(("Result".into(), vec![(**ok).clone(), (**err).clone()])),
        Type::Tuple(elems) => Some(("Tuple".into(), elems.clone())),
        Type::Record(rt) => Some((rt.name.clone(), rt.params.clone())),
        Type::Sum(st) => Some((st.name.clone(), st.type_args.clone())),
        Type::Opaque { name, params } => Some((name.clone(), params.clone())),
        Type::Stream(inner) => Some(("Stream".into(), vec![(**inner).clone()])),
        Type::Task(inner) => Some(("Task".into(), vec![(**inner).clone()])),
        Type::Actor(inner) => Some(("Actor".into(), vec![(**inner).clone()])),
        Type::Arc(inner) => Some(("Arc".into(), vec![(**inner).clone()])),
        Type::Tagged { inner, .. } => type_constructor_for_trait(inner),
        Type::App(constructor, args) => {
            let normalized = normalize_constructor_application(constructor, args)?;
            if normalized == *ty {
                None
            } else {
                type_constructor_for_trait(&normalized)
            }
        }
        Type::Existential { .. }
        | Type::AnonRecord(_)
        | Type::Function(_)
        | Type::Forall(_)
        | Type::Var(_)
        | Type::Constructor { .. }
        | Type::Row(_) => None,
    }
}

fn normalize_constructor_application(constructor: &Type, args: &[Type]) -> Option<Type> {
    match constructor {
        Type::Constructor {
            name,
            fixed_args,
            arity,
        } => {
            if *arity == 0 {
                return rebuild_type(name, &[]);
            }

            let mut slots: Vec<Option<Type>> = vec![None; *arity];
            for (idx, ty) in fixed_args {
                if *idx >= *arity {
                    return None;
                }
                slots[*idx] = Some(ty.clone());
            }

            let mut next_arg = 0usize;
            for slot in &mut slots {
                if slot.is_none() && next_arg < args.len() {
                    *slot = Some(args[next_arg].clone());
                    next_arg += 1;
                }
            }

            // Too many args for remaining holes: keep as application.
            if next_arg != args.len() {
                return Some(Type::App(
                    Box::new(Type::Constructor {
                        name: name.clone(),
                        fixed_args: fixed_args.clone(),
                        arity: *arity,
                    }),
                    args.to_vec(),
                ));
            }

            if slots.iter().all(Option::is_some) {
                let final_args: Vec<Type> = slots.into_iter().flatten().collect();
                return rebuild_type(name, &final_args);
            }

            // Still partially applied after this application.
            let updated_fixed_args: Vec<(usize, Type)> = slots
                .into_iter()
                .enumerate()
                .filter_map(|(idx, slot)| slot.map(|ty| (idx, ty)))
                .collect();
            Some(Type::Constructor {
                name: name.clone(),
                fixed_args: updated_fixed_args,
                arity: *arity,
            })
        }
        _ => Some(Type::App(Box::new(constructor.clone()), args.to_vec())),
    }
}

/// Rebuild a concrete type from a trait-dispatch constructor + arguments.
///
/// This is the inverse of [`type_constructor_for_trait`] for supported
/// built-in constructors and tuples. Named record/sum reconstruction requires
/// registry metadata (row fields / variants) and is intentionally not handled
/// here.
pub fn rebuild_type(constructor: &str, args: &[Type]) -> Option<Type> {
    Some(match constructor {
        "Int" if args.is_empty() => Type::Int,
        "Int8" if args.is_empty() => Type::IntN(IntWidth::I8, Signedness::Signed),
        "Int16" if args.is_empty() => Type::IntN(IntWidth::I16, Signedness::Signed),
        "Int32" if args.is_empty() => Type::IntN(IntWidth::I32, Signedness::Signed),
        "Int64" if args.is_empty() => Type::IntN(IntWidth::I64, Signedness::Signed),
        "UInt8" if args.is_empty() => Type::IntN(IntWidth::I8, Signedness::Unsigned),
        "UInt16" if args.is_empty() => Type::IntN(IntWidth::I16, Signedness::Unsigned),
        "UInt32" if args.is_empty() => Type::IntN(IntWidth::I32, Signedness::Unsigned),
        "UInt64" if args.is_empty() => Type::IntN(IntWidth::I64, Signedness::Unsigned),
        "Float" if args.is_empty() => Type::Float,
        "Float16" if args.is_empty() => Type::FloatN(FloatWidth::F16),
        "Float32" if args.is_empty() => Type::FloatN(FloatWidth::F32),
        "Float64" if args.is_empty() => Type::FloatN(FloatWidth::F64),
        "Bool" if args.is_empty() => Type::Bool,
        "String" if args.is_empty() => Type::String,
        "Html" if args.is_empty() => Type::Html,
        "Markdown" if args.is_empty() => Type::Markdown,
        "Unit" if args.is_empty() => Type::Unit,
        "Never" if args.is_empty() => Type::Never,
        "Atom" if args.is_empty() => Type::Atom,
        "Date" if args.is_empty() => Type::Date,
        "DateTime" if args.is_empty() => Type::DateTime,
        "Dynamic" if args.is_empty() => Type::Dynamic,
        "List" if args.len() == 1 => Type::List(Box::new(args[0].clone())),
        "Set" if args.len() == 1 => Type::Set(Box::new(args[0].clone())),
        "Option" if args.len() == 1 => Type::Option(Box::new(args[0].clone())),
        "Map" if args.len() == 2 => Type::Map(Box::new(args[0].clone()), Box::new(args[1].clone())),
        "Result" if args.len() == 2 => {
            Type::Result(Box::new(args[0].clone()), Box::new(args[1].clone()))
        }
        "Tuple" => Type::Tuple(args.to_vec()),
        "Stream" if args.len() == 1 => Type::Stream(Box::new(args[0].clone())),
        "Task" if args.len() == 1 => Type::Task(Box::new(args[0].clone())),
        "Actor" if args.len() == 1 => Type::Actor(Box::new(args[0].clone())),
        "Arc" if args.len() == 1 => Type::Arc(Box::new(args[0].clone())),
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// Sendable checking (KERNEL §13.6)
// ---------------------------------------------------------------------------

/// Check whether a type is Sendable (safe to transfer to an actor task).
///
/// Sendable types: primitives, Actor(T), Task(T), Arc(T), error types, and
/// compound types whose components are all Sendable.
/// Functions/closures are NOT Sendable.
pub fn is_sendable(ty: &Type) -> bool {
    match ty {
        // Primitives are always Sendable.
        Type::Int
        | Type::IntN(_, _)
        | Type::Float
        | Type::FloatN(_)
        | Type::Decimal { .. }
        | Type::Bool
        | Type::String
        | Type::Html
        | Type::Markdown
        | Type::Unit
        | Type::Never
        | Type::Atom
        | Type::Date
        | Type::DateTime => true,
        // Actor handles and dynamic values are Sendable.
        Type::Actor(_) | Type::Dynamic => true,
        // Arc makes anything Sendable (that's its purpose).
        Type::Arc(_) => true,
        // Tagged type follows inner.
        Type::Tagged { inner, .. } => is_sendable(inner),
        // Stream is Sendable if its element type is.
        Type::Stream(inner) => is_sendable(inner),
        // Task is Sendable if its output type is.
        Type::Task(inner) => is_sendable(inner),
        // Compound types: Sendable if all components are Sendable.
        Type::Option(inner) => is_sendable(inner),
        Type::Result(ok, err) => is_sendable(ok) && is_sendable(err),
        Type::Existential { bounds, .. } => bounds.iter().any(|b| b == "Sendable"),
        Type::Tuple(elems) => elems.iter().all(is_sendable),
        Type::List(inner)
        | Type::Set(inner)
        | Type::FixedSizeList { element: inner, .. }
        | Type::Tensor { element: inner, .. } => is_sendable(inner),
        Type::Map(k, v) => is_sendable(k) && is_sendable(v),
        // Records: Sendable if all fields are Sendable.
        Type::Record(rt) => rt.row.fields.iter().all(|(_, t)| is_sendable(t)),
        Type::AnonRecord(row) | Type::Row(row) => row.fields.iter().all(|(_, t)| is_sendable(t)),
        // Sum types: Sendable if all variant fields are Sendable.
        Type::Sum(st) => {
            st.type_args.iter().all(is_sendable)
                && st
                    .variants
                    .iter()
                    .all(|(_, fields)| fields.iter().all(is_sendable))
        }
        // Opaque wrappers are sendable if all type parameters are sendable.
        Type::Opaque { params, .. } => params.iter().all(is_sendable),
        Type::Forall(scheme) => is_sendable(&scheme.ty),
        // Functions/closures are NOT Sendable.
        Type::Function(_) => false,
        // Unresolved type variables: assume Sendable (checked when resolved).
        Type::Var(_) => true,
        // Internal constructor terms should be normalized before sendability checks.
        Type::App(_, _) | Type::Constructor { .. } => false,
    }
}

/// Describes why a type is not Sendable.
pub struct SendableViolation {
    /// Path to the offending field (e.g., "handler" or "config.callback").
    pub path: String,
    /// The non-Sendable type found.
    pub ty: Type,
    /// Human-readable reason.
    pub reason: String,
}

/// Find the first Sendable violation in a type, with a path for diagnostics.
///
/// Returns `None` if the type is Sendable.
pub fn sendable_violation(ty: &Type) -> Option<SendableViolation> {
    sendable_violation_inner(ty, "")
}

fn sendable_violation_inner(ty: &Type, path: &str) -> Option<SendableViolation> {
    match ty {
        Type::Function(_) => Some(SendableViolation {
            path: if path.is_empty() {
                "<value>".to_string()
            } else {
                path.to_string()
            },
            ty: ty.clone(),
            reason: "closures are not Sendable".to_string(),
        }),
        Type::Option(inner) => sendable_violation_inner(inner, path),
        Type::Result(ok, err) => {
            sendable_violation_inner(ok, path).or_else(|| sendable_violation_inner(err, path))
        }
        Type::Existential { bounds, .. } => {
            if bounds.iter().any(|b| b == "Sendable") {
                None
            } else {
                Some(SendableViolation {
                    path: if path.is_empty() {
                        "<value>".to_string()
                    } else {
                        path.to_string()
                    },
                    ty: ty.clone(),
                    reason: "existential type does not require Sendable".to_string(),
                })
            }
        }
        Type::Tuple(elems) => {
            for (i, t) in elems.iter().enumerate() {
                let p = if path.is_empty() {
                    format!("{i}")
                } else {
                    format!("{path}.{i}")
                };
                if let Some(v) = sendable_violation_inner(t, &p) {
                    return Some(v);
                }
            }
            None
        }
        Type::List(inner)
        | Type::Set(inner)
        | Type::FixedSizeList { element: inner, .. }
        | Type::Tensor { element: inner, .. } => sendable_violation_inner(inner, path),
        Type::Map(k, v) => {
            sendable_violation_inner(k, path).or_else(|| sendable_violation_inner(v, path))
        }
        Type::Record(rt) => {
            for (label, t) in &rt.row.fields {
                let p = if path.is_empty() {
                    label.0.clone()
                } else {
                    format!("{path}.{}", label.0)
                };
                if let Some(v) = sendable_violation_inner(t, &p) {
                    return Some(v);
                }
            }
            None
        }
        Type::AnonRecord(row) | Type::Row(row) => {
            for (label, t) in &row.fields {
                let p = if path.is_empty() {
                    label.0.clone()
                } else {
                    format!("{path}.{}", label.0)
                };
                if let Some(v) = sendable_violation_inner(t, &p) {
                    return Some(v);
                }
            }
            None
        }
        Type::Sum(st) => {
            for (i, arg) in st.type_args.iter().enumerate() {
                let p = if path.is_empty() {
                    format!("type_arg.{i}")
                } else {
                    format!("{path}.type_arg.{i}")
                };
                if let Some(v) = sendable_violation_inner(arg, &p) {
                    return Some(v);
                }
            }
            for (variant_name, fields) in &st.variants {
                for (i, t) in fields.iter().enumerate() {
                    let p = format!("{variant_name}.{i}");
                    if let Some(v) = sendable_violation_inner(t, &p) {
                        return Some(v);
                    }
                }
            }
            None
        }
        Type::Opaque { params, .. } => {
            for (i, t) in params.iter().enumerate() {
                let p = if path.is_empty() {
                    format!("param.{i}")
                } else {
                    format!("{path}.param.{i}")
                };
                if let Some(v) = sendable_violation_inner(t, &p) {
                    return Some(v);
                }
            }
            None
        }
        Type::Forall(scheme) => sendable_violation_inner(&scheme.ty, path),
        Type::Tagged { inner, .. } => sendable_violation_inner(inner, path),
        Type::Stream(inner) => sendable_violation_inner(inner, path),
        Type::Task(inner) => sendable_violation_inner(inner, path),
        Type::App(constructor, args) => {
            if let Some(normalized) = normalize_constructor_application(constructor, args) {
                sendable_violation_inner(&normalized, path)
            } else {
                Some(SendableViolation {
                    path: if path.is_empty() {
                        "<value>".to_string()
                    } else {
                        path.to_string()
                    },
                    ty: ty.clone(),
                    reason: "unresolved constructor application is not Sendable".to_string(),
                })
            }
        }
        Type::Constructor { fixed_args, .. } => {
            for (idx, arg_ty) in fixed_args {
                let p = if path.is_empty() {
                    format!("ctor.{idx}")
                } else {
                    format!("{path}.ctor.{idx}")
                };
                if let Some(v) = sendable_violation_inner(arg_ty, &p) {
                    return Some(v);
                }
            }
            Some(SendableViolation {
                path: if path.is_empty() {
                    "<value>".to_string()
                } else {
                    path.to_string()
                },
                ty: ty.clone(),
                reason: "unapplied type constructor is not Sendable".to_string(),
            })
        }
        // Explicitly list all Sendable types so adding a new Type variant
        // produces a compiler error here (forcing a Sendable decision).
        Type::Int
        | Type::IntN(_, _)
        | Type::Float
        | Type::FloatN(_)
        | Type::Decimal { .. }
        | Type::Bool
        | Type::String
        | Type::Html
        | Type::Markdown
        | Type::Unit
        | Type::Never
        | Type::Atom
        | Type::Date
        | Type::DateTime
        | Type::Dynamic
        | Type::Actor(_)
        | Type::Arc(_)
        | Type::Var(_) => None,
    }
}
// ---------------------------------------------------------------------------
// Module system (BuiltinModule trait, ModuleRegistry)
// ---------------------------------------------------------------------------

/// Describes a built-in function's type-level information.
///
/// This is the type-level half of a builtin. Eval dispatch stays in `kea-eval`
/// keyed by the function name string (the `Value::BuiltinFn(String)` pattern).
pub struct BuiltinFunctionInfo {
    pub name: &'static str,
    pub module: &'static str,
    pub type_scheme: TypeScheme,
    pub effects: Effects,
    pub doc: &'static str,
    /// Whether this function is public (exported from its module).
    /// Private functions are not visible via `import Mod` or `import Mod.{name}`.
    pub is_public: bool,
    /// Whether this function is part of the curated prelude (always available without import).
    pub is_prelude: bool,
}

/// Type-level description of a builtin module.
///
/// Implementors provide function signatures and submodule structure.
/// This trait lives in `kea-types` (not `kea-eval`) because it only
/// carries type information — no runtime values or eval logic.
pub trait BuiltinModule: Send + Sync {
    /// Fully qualified module name (e.g., `"Kea.Core"`).
    fn name(&self) -> &'static str;
    /// Functions exported by this module.
    fn functions(&self) -> Vec<BuiltinFunctionInfo>;
    /// Nested submodules.
    fn submodules(&self) -> Vec<Box<dyn BuiltinModule>> {
        Vec::new()
    }
}

/// Central registry of builtin modules. Used by REPL, MCP, and type checker
/// to discover available functions and resolve import paths.
///
/// Modules are stored flat by their fully qualified name. Submodules are
/// registered recursively at `register()` time, so `resolve()` is always
/// a simple map lookup.
pub struct ModuleRegistry {
    modules: BTreeMap<String, Box<dyn BuiltinModule>>,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self {
            modules: BTreeMap::new(),
        }
    }

    /// Register a module and all its submodules (recursively).
    ///
    /// Returns an error if a module with the same name is already registered.
    pub fn register(&mut self, module: Box<dyn BuiltinModule>) -> Result<(), String> {
        // Recursively register submodules first.
        for sub in module.submodules() {
            self.register(sub)?;
        }
        let name = module.name().to_string();
        if self.modules.contains_key(&name) {
            return Err(format!("module `{name}` is already registered"));
        }
        self.modules.insert(name, module);
        Ok(())
    }

    /// Whether the registry has any registered modules.
    pub fn is_empty(&self) -> bool {
        self.modules.is_empty()
    }

    /// Resolve a module by its fully qualified path (e.g., `"Kea.Core"`).
    pub fn resolve(&self, path: &str) -> Option<&dyn BuiltinModule> {
        self.modules.get(path).map(|m| m.as_ref())
    }

    /// Resolve a specific function within a module.
    pub fn resolve_function(&self, module_path: &str, name: &str) -> Option<BuiltinFunctionInfo> {
        let module = self.resolve(module_path)?;
        module.functions().into_iter().find(|f| f.name == name)
    }

    /// All functions from all registered modules (for prelude injection).
    pub fn all_functions(&self) -> Vec<BuiltinFunctionInfo> {
        let mut result = Vec::new();
        for module in self.modules.values() {
            result.extend(module.functions());
        }
        result
    }

    /// All registered top-level module names.
    pub fn module_names(&self) -> Vec<&str> {
        self.modules.keys().map(|s| s.as_str()).collect()
    }

    /// All registered modules.
    pub fn all_modules(&self) -> Vec<&dyn BuiltinModule> {
        self.modules.values().map(|m| m.as_ref()).collect()
    }
}

impl Default for ModuleRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Purity and volatility (tracked alongside types, not inside them)
// ---------------------------------------------------------------------------

/// Purity of a function (KERNEL §2.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Purity {
    Pure,
    Impure,
}

/// Volatility of a pure function (KERNEL §2.4).
/// Only meaningful when `Purity == Pure`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Volatility {
    Deterministic,
    Volatile,
}

/// Combined effect classification for a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Effects {
    pub purity: Purity,
    pub volatility: Volatility,
}

/// Inference variable identifier for effect-polymorphic signatures.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EffectVarId(pub u32);

impl Effects {
    pub fn pure_deterministic() -> Self {
        Self {
            purity: Purity::Pure,
            volatility: Volatility::Deterministic,
        }
    }

    pub fn pure_volatile() -> Self {
        Self {
            purity: Purity::Pure,
            volatility: Volatility::Volatile,
        }
    }

    pub fn impure() -> Self {
        Self {
            purity: Purity::Impure,
            // Volatility is irrelevant for impure functions, but we need a value.
            volatility: Volatility::Deterministic,
        }
    }

    /// Can results of this function be memoized? (KERNEL §2.4)
    pub fn is_memoizable(&self) -> bool {
        self.purity == Purity::Pure && self.volatility == Volatility::Deterministic
    }
}

impl Type {
    /// Returns true for integer scalar types (`Int`, `Int8`..`Int64`, `UInt8`..`UInt64`).
    pub fn is_integer(&self) -> bool {
        matches!(self, Type::Int | Type::IntN(_, _))
    }

    /// Returns true for signed integer scalar types (`Int`, `Int8`..`Int64`).
    pub fn is_signed_integer(&self) -> bool {
        matches!(self, Type::Int | Type::IntN(_, Signedness::Signed))
    }

    /// Returns true for floating-point scalar types (`Float`, `Float16`..`Float64`).
    pub fn is_float(&self) -> bool {
        matches!(self, Type::Float | Type::FloatN(_))
    }

    /// Returns true for fixed-point decimal scalar types.
    pub fn is_decimal(&self) -> bool {
        matches!(self, Type::Decimal { .. })
    }

    /// Returns true for numeric scalar types (all integer and float variants).
    pub fn is_numeric(&self) -> bool {
        self.is_integer() || self.is_float() || self.is_decimal()
    }

    /// Check whether this type has an Arrow/DataFusion representation.
    ///
    /// Returns `true` for scalar types that can be used as UDF parameters or
    /// return types: Int, Float, Bool, String, Unit, Date, DateTime, Option(T).
    /// This is a pure check that doesn't depend on Arrow and mirrors the
    /// scalar mapping used at the dataframe runtime boundary.
    pub fn is_arrow_scalar(&self) -> bool {
        matches!(
            self,
            Type::Bool | Type::String | Type::Unit | Type::Never | Type::Date | Type::DateTime
        ) || matches!(self, Type::Option(inner) if inner.is_arrow_scalar())
            || self.is_numeric()
    }
}

// ---------------------------------------------------------------------------
// Substitution
// ---------------------------------------------------------------------------

/// Maps type variables and row variables to their resolved types/rows.
///
/// Applied during and after unification to resolve inference variables.
#[derive(Debug, Clone, Default)]
pub struct Substitution {
    type_map: BTreeMap<TypeVarId, Type>,
    row_map: BTreeMap<RowVarId, RowType>,
    dim_map: BTreeMap<DimVarId, Dim>,
}

impl Substitution {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bind_type(&mut self, var: TypeVarId, ty: Type) {
        self.type_map.insert(var, ty);
    }

    pub fn bind_row(&mut self, var: RowVarId, row: RowType) {
        self.row_map.insert(var, row);
    }

    pub fn lookup_type(&self, var: TypeVarId) -> Option<&Type> {
        self.type_map.get(&var)
    }

    pub fn lookup_row(&self, var: RowVarId) -> Option<&RowType> {
        self.row_map.get(&var)
    }

    pub fn bind_dim(&mut self, var: DimVarId, dim: Dim) {
        self.dim_map.insert(var, dim);
    }

    pub fn lookup_dim(&self, var: DimVarId) -> Option<&Dim> {
        self.dim_map.get(&var)
    }

    pub fn type_bindings(&self) -> &BTreeMap<TypeVarId, Type> {
        &self.type_map
    }

    pub fn row_bindings(&self) -> &BTreeMap<RowVarId, RowType> {
        &self.row_map
    }

    pub fn dim_bindings(&self) -> &BTreeMap<DimVarId, Dim> {
        &self.dim_map
    }

    pub fn apply_dim(&self, dim: &Dim) -> Dim {
        match dim {
            Dim::Var(v) => match self.lookup_dim(*v) {
                Some(resolved) => self.apply_dim(resolved),
                None => dim.clone(),
            },
            known => known.clone(),
        }
    }

    /// Apply this substitution to a type, replacing all bound variables.
    pub fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(v) => match self.lookup_type(*v) {
                Some(resolved) => self.apply(resolved),
                None => ty.clone(),
            },
            Type::App(constructor, args) => {
                let resolved_constructor = self.apply(constructor);
                let resolved_args: Vec<Type> = args.iter().map(|arg| self.apply(arg)).collect();
                normalize_constructor_application(&resolved_constructor, &resolved_args)
                    .unwrap_or(Type::App(Box::new(resolved_constructor), resolved_args))
            }
            Type::Constructor {
                name,
                fixed_args,
                arity,
            } => Type::Constructor {
                name: name.clone(),
                fixed_args: fixed_args
                    .iter()
                    .map(|(idx, ty)| (*idx, self.apply(ty)))
                    .collect(),
                arity: *arity,
            },
            Type::Row(row) => Type::Row(self.apply_row(row)),
            Type::List(inner) => Type::List(Box::new(self.apply(inner))),
            Type::FixedSizeList { element, size } => Type::FixedSizeList {
                element: Box::new(self.apply(element)),
                size: self.apply_dim(size),
            },
            Type::Tensor { element, shape } => Type::Tensor {
                element: Box::new(self.apply(element)),
                shape: shape.iter().map(|dim| self.apply_dim(dim)).collect(),
            },
            Type::Set(inner) => Type::Set(Box::new(self.apply(inner))),
            Type::Option(inner) => Type::Option(Box::new(self.apply(inner))),
            Type::Map(k, v) => Type::Map(Box::new(self.apply(k)), Box::new(self.apply(v))),
            Type::Result(ok, err) => {
                Type::Result(Box::new(self.apply(ok)), Box::new(self.apply(err)))
            }
            Type::Existential {
                bounds,
                associated_types,
            } => Type::Existential {
                bounds: bounds.clone(),
                associated_types: associated_types
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.apply(ty)))
                    .collect(),
            },
            Type::Tuple(elems) => Type::Tuple(elems.iter().map(|t| self.apply(t)).collect()),
            Type::Function(ft) => Type::Function(FunctionType {
                params: ft.params.iter().map(|t| self.apply(t)).collect(),
                ret: Box::new(self.apply(&ft.ret)),
                effects: self.apply_effect_row(&ft.effects),
            }),
            Type::Forall(scheme) => {
                let mut shadowed = self.clone();
                for tv in &scheme.type_vars {
                    shadowed.type_map.remove(tv);
                }
                for rv in &scheme.row_vars {
                    shadowed.row_map.remove(rv);
                }
                for dv in &scheme.dim_vars {
                    shadowed.dim_map.remove(dv);
                }
                let mut updated = (**scheme).clone();
                updated.ty = shadowed.apply(&updated.ty);
                Type::Forall(Box::new(updated))
            }
            Type::Record(rt) => Type::Record(RecordType {
                name: rt.name.clone(),
                params: rt.params.iter().map(|t| self.apply(t)).collect(),
                row: self.apply_row(&rt.row),
            }),
            Type::Opaque { name, params } => Type::Opaque {
                name: name.clone(),
                params: params.iter().map(|t| self.apply(t)).collect(),
            },
            Type::AnonRecord(row) => Type::AnonRecord(self.apply_row(row)),
            Type::Sum(st) => Type::Sum(SumType {
                name: st.name.clone(),
                type_args: st.type_args.iter().map(|t| self.apply(t)).collect(),
                variants: st
                    .variants
                    .iter()
                    .map(|(vname, fields)| {
                        (
                            vname.clone(),
                            fields.iter().map(|t| self.apply(t)).collect(),
                        )
                    })
                    .collect(),
            }),
            Type::Tagged { inner, tags } => Type::Tagged {
                inner: Box::new(self.apply(inner)),
                tags: tags.clone(),
            },
            Type::Decimal { precision, scale } => Type::Decimal {
                precision: self.apply_dim(precision),
                scale: self.apply_dim(scale),
            },
            Type::Stream(inner) => Type::Stream(Box::new(self.apply(inner))),
            Type::Task(inner) => Type::Task(Box::new(self.apply(inner))),
            Type::Actor(inner) => Type::Actor(Box::new(self.apply(inner))),
            Type::Arc(inner) => Type::Arc(Box::new(self.apply(inner))),
            // Leaves: no substitution needed.
            Type::Int
            | Type::IntN(_, _)
            | Type::Float
            | Type::FloatN(_)
            | Type::Bool
            | Type::String
            | Type::Html
            | Type::Markdown
            | Type::Unit
            | Type::Never
            | Type::Atom
            | Type::Date
            | Type::DateTime
            | Type::Dynamic => ty.clone(),
        }
    }

    /// Apply this substitution to a row type.
    pub fn apply_row(&self, row: &RowType) -> RowType {
        let fields: Vec<(Label, Type)> = row
            .fields
            .iter()
            .map(|(l, t)| (l.clone(), self.apply(t)))
            .collect();

        match row.rest {
            None => RowType { fields, rest: None },
            Some(var) => match self.lookup_row(var) {
                Some(resolved) => {
                    // Merge the resolved row's fields with our known fields.
                    let resolved = self.apply_row(resolved);
                    let mut all_fields = fields;
                    all_fields.extend(resolved.fields);
                    all_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                    RowType {
                        fields: all_fields,
                        rest: resolved.rest,
                    }
                }
                None => RowType {
                    fields,
                    rest: Some(var),
                },
            },
        }
    }

    pub fn apply_effect_row(&self, effects: &EffectRow) -> EffectRow {
        EffectRow {
            row: self.apply_row(&effects.row),
        }
    }
}

// ---------------------------------------------------------------------------
// Lacks constraints
// ---------------------------------------------------------------------------

/// Tracks which labels each row variable must lack (KERNEL §2.2).
///
/// When a row is extended with label `l`, the row variable must lack `l`.
/// This prevents duplicate labels.
#[derive(Debug, Clone, Default)]
pub struct LacksConstraints {
    constraints: BTreeMap<RowVarId, BTreeSet<Label>>,
}

impl LacksConstraints {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record that `var` must lack `label`.
    pub fn add(&mut self, var: RowVarId, label: Label) {
        self.constraints.entry(var).or_default().insert(label);
    }

    /// Check whether `var` is known to lack `label`.
    pub fn lacks(&self, var: RowVarId, label: &Label) -> bool {
        self.constraints
            .get(&var)
            .is_some_and(|labels| labels.contains(label))
    }

    /// Get all labels that `var` must lack.
    pub fn get(&self, var: RowVarId) -> Option<&BTreeSet<Label>> {
        self.constraints.get(&var)
    }

    /// Transfer all lacks constraints from `from` to `to`.
    /// Used when unification binds one row variable to another.
    pub fn transfer(&mut self, from: RowVarId, to: RowVarId) {
        if let Some(labels) = self.constraints.remove(&from) {
            self.constraints.entry(to).or_default().extend(labels);
        }
    }

    /// Check whether adding `label` to a row with variable `var` would violate constraints.
    /// Returns `true` if the extension is allowed (var does not lack the label).
    pub fn can_extend(&self, var: RowVarId, label: &Label) -> bool {
        !self.lacks(var, label)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn row_type_closed() {
        let row = RowType::closed(vec![
            (Label::new("b"), Type::Int),
            (Label::new("a"), Type::String),
        ]);
        assert!(row.is_closed());
        // Fields should be sorted.
        assert_eq!(row.fields[0].0, Label::new("a"));
        assert_eq!(row.fields[1].0, Label::new("b"));
    }

    #[test]
    fn row_type_lookup() {
        let row = RowType::closed(vec![
            (Label::new("name"), Type::String),
            (Label::new("age"), Type::Int),
        ]);
        assert_eq!(row.get(&Label::new("name")), Some(&Type::String));
        assert_eq!(row.get(&Label::new("age")), Some(&Type::Int));
        assert_eq!(row.get(&Label::new("missing")), None);
    }

    #[test]
    fn substitution_apply_basic() {
        let mut subst = Substitution::new();
        subst.bind_type(TypeVarId(0), Type::Int);

        let ty = Type::Var(TypeVarId(0));
        assert_eq!(subst.apply(&ty), Type::Int);
    }

    #[test]
    fn substitution_apply_nested() {
        let mut subst = Substitution::new();
        subst.bind_type(TypeVarId(0), Type::Int);

        let ty = Type::List(Box::new(Type::Var(TypeVarId(0))));
        assert_eq!(subst.apply(&ty), Type::List(Box::new(Type::Int)));
    }

    #[test]
    fn substitution_apply_row() {
        let mut subst = Substitution::new();
        subst.bind_row(
            RowVarId(0),
            RowType::closed(vec![(Label::new("extra"), Type::Bool)]),
        );

        let row = RowType::open(vec![(Label::new("name"), Type::String)], RowVarId(0));
        let resolved = subst.apply_row(&row);

        assert!(resolved.is_closed());
        assert_eq!(resolved.fields.len(), 2);
        assert!(resolved.has(&Label::new("name")));
        assert!(resolved.has(&Label::new("extra")));
    }

    #[test]
    fn substitution_apply_dim_basic() {
        let mut subst = Substitution::new();
        subst.bind_dim(DimVarId(0), Dim::Known(768));

        assert_eq!(subst.apply_dim(&Dim::Var(DimVarId(0))), Dim::Known(768));
    }

    #[test]
    fn substitution_apply_dim_chain() {
        let mut subst = Substitution::new();
        subst.bind_dim(DimVarId(0), Dim::Var(DimVarId(1)));
        subst.bind_dim(DimVarId(1), Dim::Known(32));

        assert_eq!(subst.apply_dim(&Dim::Var(DimVarId(0))), Dim::Known(32));
    }

    #[test]
    fn substitution_apply_forall_shadows_dim_vars() {
        let mut subst = Substitution::new();
        subst.bind_dim(DimVarId(0), Dim::Known(64));

        let ty = Type::Forall(Box::new(TypeScheme {
            type_vars: vec![],
            row_vars: vec![],
            dim_vars: vec![DimVarId(0)],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: BTreeMap::new(),
            ty: Type::Tensor {
                element: Box::new(Type::Int),
                shape: vec![Dim::Var(DimVarId(0))],
            },
        }));

        let resolved = subst.apply(&ty);
        match resolved {
            Type::Forall(scheme) => match scheme.ty {
                Type::Tensor { shape, .. } => {
                    assert_eq!(shape, vec![Dim::Var(DimVarId(0))]);
                }
                other => panic!("expected Tensor body under forall, got {other:?}"),
            },
            other => panic!("expected forall type, got {other:?}"),
        }
    }

    #[test]
    fn type_scheme_is_mono_checks_dim_vars() {
        let mono = TypeScheme::mono(Type::Int);
        assert!(mono.is_mono());

        let poly_dim = TypeScheme {
            type_vars: vec![],
            row_vars: vec![],
            dim_vars: vec![DimVarId(0)],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: BTreeMap::new(),
            ty: Type::Int,
        };
        assert!(!poly_dim.is_mono());
    }

    #[test]
    fn lacks_constraints_basic() {
        let mut lacks = LacksConstraints::new();
        let var = RowVarId(0);
        let label = Label::new("name");

        assert!(lacks.can_extend(var, &label));
        lacks.add(var, label.clone());
        assert!(!lacks.can_extend(var, &label));
    }

    #[test]
    fn effects_classification_helpers() {
        let pure = Effects::pure_deterministic();
        let volatile = Effects::pure_volatile();
        let impure = Effects::impure();

        assert!(pure.is_memoizable());
        assert!(!volatile.is_memoizable());
        assert!(!impure.is_memoizable());
    }

    #[test]
    fn display_primitives() {
        assert_eq!(Type::Int.to_string(), "Int");
        assert_eq!(Type::Float.to_string(), "Float");
        assert_eq!(
            Type::Decimal {
                precision: Dim::Known(18),
                scale: Dim::Known(2)
            }
            .to_string(),
            "Decimal(18, 2)"
        );
        assert_eq!(Type::Bool.to_string(), "Bool");
        assert_eq!(Type::String.to_string(), "String");
        assert_eq!(Type::Unit.to_string(), "()");
        assert_eq!(Type::Never.to_string(), "Never");
    }

    #[test]
    fn numeric_type_helpers_cover_precision_variants() {
        assert!(Type::Int.is_integer());
        assert!(Type::Int.is_signed_integer());
        assert!(Type::IntN(IntWidth::I16, Signedness::Signed).is_integer());
        assert!(Type::IntN(IntWidth::I16, Signedness::Signed).is_signed_integer());
        assert!(Type::IntN(IntWidth::I8, Signedness::Unsigned).is_integer());
        assert!(!Type::IntN(IntWidth::I8, Signedness::Unsigned).is_signed_integer());
        assert!(Type::Float.is_float());
        assert!(Type::FloatN(FloatWidth::F32).is_float());
        assert!(
            Type::Decimal {
                precision: Dim::Known(18),
                scale: Dim::Known(2)
            }
            .is_decimal()
        );
        assert!(Type::FloatN(FloatWidth::F16).is_numeric());
        assert!(Type::IntN(IntWidth::I32, Signedness::Signed).is_numeric());
        assert!(
            Type::Decimal {
                precision: Dim::Known(18),
                scale: Dim::Known(2)
            }
            .is_numeric()
        );
        assert!(!Type::String.is_numeric());
    }

    #[test]
    fn display_compound() {
        assert_eq!(Type::List(Box::new(Type::Int)).to_string(), "List(Int)");
        assert_eq!(Type::Option(Box::new(Type::String)).to_string(), "String?");
        assert_eq!(
            Type::Tuple(vec![Type::Int, Type::String]).to_string(),
            "#(Int, String)"
        );
        assert_eq!(
            Type::Result(Box::new(Type::Int), Box::new(Type::String)).to_string(),
            "Result(Int, String)"
        );
    }

    #[test]
    fn display_existential() {
        let mut assoc = BTreeMap::new();
        assoc.insert("Item".to_string(), Type::Int);
        assert_eq!(
            Type::Existential {
                bounds: vec!["Show".to_string(), "Eq".to_string()],
                associated_types: assoc,
            }
            .to_string(),
            "any (Show, Eq) where Item = Int"
        );
    }

    #[test]
    fn display_function() {
        let ft = Type::Function(FunctionType {
            params: vec![Type::Int, Type::Bool],
            ret: Box::new(Type::String),
            effects: EffectRow::pure(),
        });
        assert_eq!(ft.to_string(), "(Int, Bool) -> String");
    }

    #[test]
    fn display_anon_record() {
        let row = RowType::closed(vec![
            (Label::new("age"), Type::Int),
            (Label::new("name"), Type::String),
        ]);
        let ty = Type::AnonRecord(row);
        assert_eq!(ty.to_string(), "#{ age: Int, name: String }");
    }

    #[test]
    fn display_kind_eff() {
        assert_eq!(Kind::Eff.to_string(), "Eff");
        assert_eq!(Kind::Star.to_string(), "*");
    }

    #[test]
    fn effect_row_display_and_sorting() {
        let effects = EffectRow::closed(vec![
            (Label::new("Fail"), Type::String),
            (Label::new("IO"), Type::Unit),
        ]);
        assert_eq!(effects.to_string(), "[Fail(String), IO]");
    }

    #[test]
    fn effect_row_open_tail_displays_evar() {
        let effects = EffectRow::open(vec![(Label::new("IO"), Type::Unit)], RowVarId(7));
        assert_eq!(effects.to_string(), "[IO | e7]");
    }

    #[test]
    fn effect_row_pure_is_empty_closed() {
        let effects = EffectRow::pure();
        assert!(effects.is_pure());
        assert_eq!(effects.to_string(), "[]");
    }

    #[test]
    fn handler_type_display() {
        let handler = HandlerType {
            handled: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
            input: Box::new(Type::Int),
            output: Box::new(Type::String),
        };
        assert_eq!(handler.to_string(), "handler Int -[IO]> String");
    }

    #[test]
    fn display_type_var() {
        assert_eq!(Type::Var(TypeVarId(0)).to_string(), "t0");
        assert_eq!(Type::Var(TypeVarId(42)).to_string(), "t42");
    }

    #[test]
    fn sanitize_type_pair_display_uses_shared_namespace() {
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
        let (expected_s, actual_s) = sanitize_type_pair_display(&expected, &actual);

        assert_eq!(expected_s, "(Int, Int) -> b");
        assert_eq!(actual_s, "(a) -> a");
    }

    #[test]
    fn sanitize_type_display_sanitizes_row_vars() {
        let ty = Type::AnonRecord(RowType::open(
            vec![(Label::new("x"), Type::Int)],
            RowVarId(12),
        ));
        let rendered = sanitize_type_display(&ty);
        assert_eq!(rendered, "#{ x: Int | ra }");
    }

    #[test]
    fn sanitize_type_display_sanitizes_dim_vars() {
        let ty = Type::Decimal {
            precision: Dim::Var(DimVarId(42)),
            scale: Dim::Var(DimVarId(99)),
        };
        let rendered = sanitize_type_display(&ty);
        assert_eq!(rendered, "Decimal");
    }

    #[test]
    fn sanitize_type_display_collapses_nested_decimal_dim_vars() {
        let ty = Type::List(Box::new(Type::Decimal {
            precision: Dim::Var(DimVarId(3)),
            scale: Dim::Var(DimVarId(4)),
        }));
        let rendered = sanitize_type_display(&ty);
        assert_eq!(rendered, "List(Decimal)");
    }

    #[test]
    fn tagged_display_preserves_wrapper() {
        // Empty-tag Tagged must show Tagged(T), not just T
        let ty = Type::Tagged {
            inner: Box::new(Type::Int),
            tags: BTreeMap::new(),
        };
        assert_eq!(ty.to_string(), "Tagged(Int)");
        assert_eq!(sanitize_type_display(&ty), "Tagged(Int)");

        // Tagged with tags uses the `T :: { k: v }` syntax
        let ty_with_tags = Type::Tagged {
            inner: Box::new(Type::Int),
            tags: BTreeMap::from([("unit".to_string(), 1)]),
        };
        assert_eq!(ty_with_tags.to_string(), "Int :: {unit: 1}");
    }

    #[test]
    fn lacks_constraints_transfer() {
        let mut lacks = LacksConstraints::new();
        let var_a = RowVarId(0);
        let var_b = RowVarId(1);

        lacks.add(var_a, Label::new("x"));
        lacks.add(var_a, Label::new("y"));
        lacks.add(var_b, Label::new("z"));

        lacks.transfer(var_a, var_b);

        // var_b should now lack x, y, and z.
        assert!(lacks.lacks(var_b, &Label::new("x")));
        assert!(lacks.lacks(var_b, &Label::new("y")));
        assert!(lacks.lacks(var_b, &Label::new("z")));
    }

    // -- ModuleRegistry tests --

    /// A test module with two functions.
    struct TestModule;

    impl BuiltinModule for TestModule {
        fn name(&self) -> &'static str {
            "Test.Math"
        }

        fn functions(&self) -> Vec<BuiltinFunctionInfo> {
            vec![
                BuiltinFunctionInfo {
                    name: "sqrt",
                    module: "Kea.Math",
                    type_scheme: TypeScheme::mono(Type::Function(FunctionType {
                        params: vec![Type::Float],
                        ret: Box::new(Type::Float),
                        effects: EffectRow::pure(),
                    })),
                    effects: Effects::pure_deterministic(),
                    doc: "Square root",
                    is_public: true,
                    is_prelude: false,
                },
                BuiltinFunctionInfo {
                    name: "abs",
                    module: "Kea.Math",
                    type_scheme: TypeScheme::mono(Type::Function(FunctionType {
                        params: vec![Type::Int],
                        ret: Box::new(Type::Int),
                        effects: EffectRow::pure(),
                    })),
                    effects: Effects::pure_deterministic(),
                    doc: "Absolute value",
                    is_public: true,
                    is_prelude: false,
                },
            ]
        }
    }

    #[test]
    fn registry_register_and_resolve() {
        let mut reg = ModuleRegistry::new();
        reg.register(Box::new(TestModule)).unwrap();
        assert!(reg.resolve("Test.Math").is_some());
        assert!(reg.resolve("Test.Missing").is_none());
    }

    #[test]
    fn registry_resolve_function() {
        let mut reg = ModuleRegistry::new();
        reg.register(Box::new(TestModule)).unwrap();
        let f = reg.resolve_function("Test.Math", "sqrt");
        assert!(f.is_some());
        assert_eq!(f.unwrap().name, "sqrt");
        assert!(reg.resolve_function("Test.Math", "missing").is_none());
    }

    #[test]
    fn registry_all_functions() {
        let mut reg = ModuleRegistry::new();
        reg.register(Box::new(TestModule)).unwrap();
        let all = reg.all_functions();
        assert_eq!(all.len(), 2);
        let names: Vec<&str> = all.iter().map(|f| f.name).collect();
        assert!(names.contains(&"sqrt"));
        assert!(names.contains(&"abs"));
    }

    #[test]
    fn registry_module_names() {
        let mut reg = ModuleRegistry::new();
        reg.register(Box::new(TestModule)).unwrap();
        let names = reg.module_names();
        assert_eq!(names, vec!["Test.Math"]);
    }

    #[test]
    fn registry_empty() {
        let reg = ModuleRegistry::new();
        assert!(reg.resolve("anything").is_none());
        assert!(reg.all_functions().is_empty());
        assert!(reg.module_names().is_empty());
    }

    #[test]
    fn type_constructor_for_trait_extracts_params() {
        let ty = Type::Map(
            Box::new(Type::String),
            Box::new(Type::List(Box::new(Type::Int))),
        );
        let (name, args) = type_constructor_for_trait(&ty).expect("constructor");
        assert_eq!(name, "Map");
        assert_eq!(args, vec![Type::String, Type::List(Box::new(Type::Int)),]);
    }

    #[test]
    fn type_constructor_for_trait_extracts_record_params() {
        let ty = Type::Record(RecordType {
            name: "Box".to_string(),
            params: vec![Type::Int],
            row: RowType::closed(vec![(Label::new("value"), Type::Int)]),
        });
        let (name, args) = type_constructor_for_trait(&ty).expect("constructor");
        assert_eq!(name, "Box");
        assert_eq!(args, vec![Type::Int]);
        assert_eq!(ty.to_string(), "Box(Int)");
    }

    #[test]
    fn type_constructor_for_trait_rejects_structural_types() {
        assert!(type_constructor_for_trait(&Type::AnonRecord(RowType::empty_closed())).is_none());
        assert!(
            type_constructor_for_trait(&Type::Function(FunctionType {
                params: vec![Type::Int],
                ret: Box::new(Type::Int),
                effects: EffectRow::pure(),
            }))
            .is_none()
        );
    }

    #[test]
    fn rebuild_type_round_trips_supported_constructors() {
        let samples = vec![
            Type::Int,
            Type::String,
            Type::List(Box::new(Type::Int)),
            Type::Option(Box::new(Type::Float)),
            Type::Map(Box::new(Type::String), Box::new(Type::Int)),
            Type::Result(Box::new(Type::Int), Box::new(Type::String)),
            Type::Stream(Box::new(Type::Bool)),
            Type::Tuple(vec![Type::Int, Type::String]),
        ];

        for ty in samples {
            let (name, args) = type_constructor_for_trait(&ty).expect("constructor");
            let rebuilt = rebuild_type(&name, &args).expect("rebuilt");
            assert_eq!(rebuilt, ty, "roundtrip failed for constructor {name}");
        }
    }

    #[test]
    fn rebuild_type_rejects_wrong_arity_and_unknown_constructor() {
        assert!(rebuild_type("List", &[]).is_none());
        assert!(rebuild_type("Result", &[Type::Int]).is_none());
        assert!(rebuild_type("UnknownType", &[]).is_none());
    }

    // -- Sendable tests --

    #[test]
    fn sendable_primitives() {
        assert!(is_sendable(&Type::Int));
        assert!(is_sendable(&Type::Float));
        assert!(is_sendable(&Type::Bool));
        assert!(is_sendable(&Type::String));
        assert!(is_sendable(&Type::Unit));
    }

    #[test]
    fn sendable_actor_and_task() {
        assert!(is_sendable(&Type::Actor(Box::new(Type::Int))));
        assert!(is_sendable(&Type::Task(Box::new(Type::Int))));
    }

    #[test]
    fn sendable_error_types() {
        assert!(is_sendable(
            &builtin_error_sum_type("IOError").expect("builtin error type")
        ));
        assert!(is_sendable(
            &builtin_error_sum_type("SchemaError").expect("builtin error type")
        ));
        assert!(is_sendable(
            &builtin_error_sum_type("ExecError").expect("builtin error type")
        ));
    }

    #[test]
    fn sendable_arc_wraps_anything() {
        // Arc(Function) IS Sendable — Arc makes anything Sendable.
        let closure_type = Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        });
        assert!(!is_sendable(&closure_type));
        assert!(is_sendable(&Type::Arc(Box::new(closure_type))));
    }

    #[test]
    fn sendable_compound_types() {
        assert!(is_sendable(&Type::Option(Box::new(Type::Int))));
        assert!(is_sendable(&Type::Result(
            Box::new(Type::Int),
            Box::new(builtin_error_sum_type("IOError").expect("builtin error type"))
        )));
        assert!(is_sendable(&Type::Tuple(vec![Type::Int, Type::String])));
        assert!(is_sendable(&Type::List(Box::new(Type::Bool))));
        assert!(is_sendable(&Type::Set(Box::new(Type::Int))));
        assert!(is_sendable(&Type::Map(
            Box::new(Type::String),
            Box::new(Type::Int)
        )));
        assert!(is_sendable(&Type::Existential {
            bounds: vec!["Sendable".to_string()],
            associated_types: BTreeMap::new(),
        }));
        assert!(!is_sendable(&Type::Existential {
            bounds: vec!["Show".to_string()],
            associated_types: BTreeMap::new(),
        }));
    }

    #[test]
    fn not_sendable_function() {
        let ft = Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Bool),
            effects: EffectRow::pure(),
        });
        assert!(!is_sendable(&ft));
    }

    #[test]
    fn not_sendable_record_with_closure_field() {
        let ft = Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        });
        let row = RowType::closed(vec![
            (Label::new("name"), Type::String),
            (Label::new("handler"), ft),
        ]);
        assert!(!is_sendable(&Type::AnonRecord(row)));
    }

    #[test]
    fn not_sendable_list_of_functions() {
        let ft = Type::Function(FunctionType {
            params: vec![],
            ret: Box::new(Type::Unit),
            effects: EffectRow::pure(),
        });
        assert!(!is_sendable(&Type::List(Box::new(ft))));
    }

    #[test]
    fn sendable_record_all_primitive_fields() {
        let row = RowType::closed(vec![
            (Label::new("age"), Type::Int),
            (Label::new("name"), Type::String),
        ]);
        assert!(is_sendable(&Type::AnonRecord(row)));
    }

    #[test]
    fn sendable_violation_reports_path() {
        let ft = Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        });
        let row = RowType::closed(vec![
            (Label::new("callback"), ft),
            (Label::new("name"), Type::String),
        ]);
        let ty = Type::AnonRecord(row);
        let violation = sendable_violation(&ty);
        assert!(violation.is_some());
        let v = violation.unwrap();
        assert_eq!(v.path, "callback");
        assert!(v.reason.contains("closures"));
    }

    #[test]
    fn sendable_violation_nested_path() {
        let ft = Type::Function(FunctionType {
            params: vec![],
            ret: Box::new(Type::Unit),
            effects: EffectRow::pure(),
        });
        let inner_row = RowType::closed(vec![(Label::new("action"), ft)]);
        let outer_row = RowType::closed(vec![
            (Label::new("config"), Type::AnonRecord(inner_row)),
            (Label::new("name"), Type::String),
        ]);
        let ty = Type::AnonRecord(outer_row);
        let violation = sendable_violation(&ty);
        assert!(violation.is_some());
        let v = violation.unwrap();
        assert_eq!(v.path, "config.action");
    }

    #[test]
    fn sendable_violation_none_for_sendable() {
        assert!(sendable_violation(&Type::Int).is_none());
        assert!(sendable_violation(&Type::Actor(Box::new(Type::Unit))).is_none());
    }

    #[test]
    fn actor_error_has_four_variants() {
        let ty = builtin_error_sum_type("ActorError").expect("ActorError should exist");
        let Type::Sum(sum) = ty else {
            panic!("ActorError should be a Sum type");
        };
        assert_eq!(sum.name, "ActorError");
        assert_eq!(sum.variants.len(), 4, "ActorError should have 4 variants");

        let expected = [
            ("Dead", vec![Type::String]),
            ("MailboxFull", vec![Type::String]),
            ("Timeout", vec![Type::String]),
            ("Custom", vec![Type::String]),
        ];
        for (name, fields) in &expected {
            let found = sum.variants.iter().find(|(n, _)| n == name);
            assert!(found.is_some(), "missing variant: {name}");
            assert_eq!(
                &found.unwrap().1,
                fields,
                "variant {name} should carry String"
            );
        }
    }
}
