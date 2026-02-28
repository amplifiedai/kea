//! AST node definitions and source spans for Kea.
//!
//! This crate defines the abstract syntax tree produced by the parser.
//! Every node carries a [`Span`] for source location tracking.

/// Identifies a source file in the compilation session.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId(pub u32);

/// A byte offset range within a source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(file: FileId, start: u32, end: u32) -> Self {
        Self { file, start, end }
    }

    /// Create a span that covers both `self` and `other`.
    pub fn merge(self, other: Span) -> Span {
        debug_assert_eq!(
            self.file, other.file,
            "cannot merge spans from different files"
        );
        Span {
            file: self.file,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// A synthetic span for compiler-generated nodes.
    pub fn synthetic() -> Self {
        Self {
            file: FileId(u32::MAX),
            start: 0,
            end: 0,
        }
    }
}

/// A value paired with its source location.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: Span) -> Self {
        Self { node, span }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
        Spanned {
            node: f(self.node),
            span: self.span,
        }
    }
}

// ---------------------------------------------------------------------------
// Literal values
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Int(i64),
    Float(f64),
    Bool(bool),
    String(String),
    Unit,
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

pub type Expr = Spanned<ExprKind>;

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// Literal value.
    Lit(Lit),

    /// Variable reference.
    Var(String),

    /// Let binding: `let pattern = value` (body is the subsequent expression).
    Let {
        pattern: Pattern,
        annotation: Option<Spanned<TypeAnnotation>>,
        value: Box<Expr>,
    },

    /// Lambda: `|params| body`.
    Lambda {
        params: Vec<Param>,
        body: Box<Expr>,
        return_annotation: Option<Spanned<TypeAnnotation>>,
    },

    /// Function application: `func(args)`.
    Call {
        func: Box<Expr>,
        args: Vec<Argument>,
    },

    /// If expression: `if cond { then } else { otherwise }`.
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },

    /// Case expression: `case scrutinee { arms }`.
    Case {
        scrutinee: Box<Expr>,
        arms: Vec<CaseArm>,
    },

    /// Scrutinee-free conditional: `cond { condition -> body, _ -> fallback }`.
    Cond { arms: Vec<CondArm> },

    /// For comprehension: `for x in xs, x > 0 { x * 2 } [into Set]`.
    For(ForExpr),

    /// Use expression: `use pattern <- expr` or `use <- expr`.
    Use(UseExpr),

    /// Handle expression: `handle expr ...` with operation clauses and optional `then`.
    Handle {
        expr: Box<Expr>,
        clauses: Vec<HandleClause>,
        then_clause: Option<Box<Expr>>,
    },

    /// Resume from inside a handler clause: `resume value`.
    Resume { value: Box<Expr> },

    /// Binary operator: `left op right`.
    BinaryOp {
        op: Spanned<BinOp>,
        left: Box<Expr>,
        right: Box<Expr>,
    },

    /// Unary operator: `op operand`.
    UnaryOp {
        op: Spanned<UnaryOp>,
        operand: Box<Expr>,
    },

    /// Postfix guard: `expr when condition`.
    WhenGuard {
        body: Box<Expr>,
        condition: Box<Expr>,
    },

    /// Range literal: `start..end` or `start..=end`.
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
        inclusive: bool,
    },

    /// Type ascription: `expr as Type`.
    As {
        expr: Box<Expr>,
        annotation: Spanned<TypeAnnotation>,
    },

    /// Tuple: `(a, b, c)`.
    Tuple(Vec<Expr>),

    /// List: `[a, b, c]`.
    List(Vec<Expr>),

    /// Named record construction: `User { name: "alice", age: 30 }`.
    Record {
        name: Spanned<String>,
        fields: Vec<(Spanned<String>, Expr)>,
        spread: Option<Box<Expr>>,
    },

    /// Functional update: `base~{ field: value }`.
    Update {
        base: Box<Expr>,
        fields: Vec<(Spanned<String>, Expr)>,
    },

    /// Anonymous record: `#{ name: "alice", age: 30 }` or `#{ ..base, x: 1 }`.
    AnonRecord {
        fields: Vec<(Spanned<String>, Expr)>,
        spread: Option<Box<Expr>>,
    },

    /// Field access: `expr.field`.
    FieldAccess {
        expr: Box<Expr>,
        field: Spanned<String>,
    },

    /// Block of expressions. Value is the last expression.
    Block(Vec<Expr>),

    /// `None` literal (general Kea expressions).
    None,

    /// Constructor application: `Some(x)`, `Ok(v)`, `Err(e)`.
    Constructor {
        name: Spanned<String>,
        args: Vec<Argument>,
    },

    /// Atom literal: `:name`. A compile-time symbol.
    Atom(String),

    /// String interpolation: `"hello ${name}"`.
    StringInterp(Vec<StringInterpPart>),

    /// Map literal: `%{"key" => value}`.
    MapLiteral(Vec<(Expr, Expr)>),

    /// Spawn an actor: `spawn <expr>` or `spawn <expr> with { ... }`.
    /// The value expression must be Sendable.
    Spawn {
        value: Box<Expr>,
        config: Option<Box<SpawnConfig>>,
    },

    /// Await a spawned task.
    /// `safe: false` = `await task` (extract or propagate crash),
    /// `safe: true` = `await? task` (Result-returning).
    Await { expr: Box<Expr>, safe: bool },

    /// Stream generator block: `stream { ... }` or `stream { ... } with { buffer: n }`.
    /// The body may contain `yield` and `yield_from` expressions.
    StreamBlock {
        body: Box<Expr>,
        /// Internal channel buffer size. Defaults to 32.
        buffer_size: usize,
    },

    /// Yield a value from inside a stream block: `yield expr`.
    Yield { value: Box<Expr> },

    /// Forward values from another stream: `yield_from expr`.
    YieldFrom { source: Box<Expr> },

    /// Send to an actor.
    ///
    /// Preferred form: `send(actor, Message)`. Internally this dispatches to
    /// `handle(message)`.
    ///
    /// Legacy form `send(actor, :method, args...)` is still represented here.
    ActorSend {
        actor: Box<Expr>,
        method: Spanned<String>,
        args: Vec<Expr>,
        /// `false` = `send(...)` (fire-and-forget),
        /// `true` = `send?(...)` or `try_send(...)` (Result-returning).
        safe: bool,
    },

    /// Call an actor operation.
    ///
    /// Preferred form: `call(actor, Message)`. Internally this dispatches to
    /// `handle(message)`.
    ///
    /// Legacy form `call(actor, :method, args...)` is still represented here.
    ActorCall {
        actor: Box<Expr>,
        method: Spanned<String>,
        args: Vec<Expr>,
        /// `false` = `call(...)` (extract or propagate crash),
        /// `true` = `call?(...)` (Result-returning).
        safe: bool,
    },

    /// Send a control signal to an actor: `control_send(actor, signal)`.
    /// Fire-and-forget, higher priority than normal mailbox.
    ControlSend { actor: Box<Expr>, signal: Box<Expr> },

    /// `_` catch-all marker used in `cond` arm conditions.
    Wildcard,
}

/// A part of a string interpolation expression.
#[derive(Debug, Clone, PartialEq)]
pub enum StringInterpPart {
    /// Literal text segment.
    Literal(String),
    /// An embedded expression.
    Expr(Box<Expr>),
}

// ---------------------------------------------------------------------------
// Patterns
// ---------------------------------------------------------------------------

pub type Pattern = Spanned<PatternKind>;

#[derive(Debug, Clone, PartialEq)]
pub enum PatternKind {
    /// Matches anything, binds nothing.
    Wildcard,

    /// Binds the matched value to a name.
    Var(String),

    /// Matches a literal value.
    Lit(Lit),

    /// Matches a sum type constructor: `Some(x)`, `Err(e)`.
    /// When `qualifier` is `Some("Type")`, this is a qualified constructor
    /// pattern: `Type.Variant(args)`.
    Constructor {
        name: String,
        qualifier: Option<String>,
        args: Vec<ConstructorFieldPattern>,
        rest: bool,
    },

    /// Matches a tuple: `(a, b)`.
    Tuple(Vec<Pattern>),

    /// Matches a named record: `User { name, .. }`.
    Record {
        name: String,
        fields: Vec<(String, Pattern)>,
        rest: bool,
    },

    /// Matches an anonymous record: `#{ name, .. }`.
    AnonRecord {
        fields: Vec<(String, Pattern)>,
        rest: bool,
    },

    /// Matches if any sub-pattern matches: `Red | Blue | Green`.
    Or(Vec<Pattern>),

    /// Binds the whole value AND destructures: `pattern as name`.
    As {
        pattern: Box<Pattern>,
        name: Spanned<String>,
    },

    /// Matches a list: `[]`, `[x]`, `[x, y]`, `[head, ..tail]`.
    List {
        /// Fixed element patterns at the front.
        elements: Vec<Pattern>,
        /// Optional rest/tail pattern (`..tail` part). If present, matches
        /// the remaining elements as a list.
        rest: Option<Box<Pattern>>,
    },
}

impl PatternKind {
    /// Returns the variable name if this is a simple `Var` pattern.
    pub fn as_var(&self) -> Option<&str> {
        match self {
            PatternKind::Var(name) => Some(name.as_str()),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Supporting types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub struct CaseArm {
    pub pattern: Pattern,
    pub guard: Option<Box<Expr>>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CondArm {
    pub condition: Box<Expr>,
    pub body: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ForExpr {
    pub clauses: Vec<ForClause>,
    pub body: Box<Expr>,
    pub into_type: Option<Spanned<TypeAnnotation>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct UseExpr {
    pub pattern: Option<Pattern>,
    pub rhs: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HandleClause {
    pub effect: Spanned<String>,
    pub operation: Spanned<String>,
    pub args: Vec<Pattern>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ForClause {
    Generator { pattern: Pattern, source: Box<Expr> },
    Guard(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Argument {
    pub label: Option<Spanned<String>>,
    pub value: Expr,
}

/// A declaration/field annotation.
///
/// Examples:
/// - `@deprecated`
/// - `@rename("user_name")`
/// - `@tagged(style: :internal, field: "type")`
#[derive(Debug, Clone, PartialEq)]
pub struct Annotation {
    pub name: Spanned<String>,
    pub args: Vec<Argument>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConstructorFieldPattern {
    pub name: Option<Spanned<String>>,
    pub pattern: Pattern,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamLabel {
    /// `_` prefix: positional-only parameter.
    Positional,
    /// `borrow` parameter convention prefix (`borrow x: T`).
    Borrow,
    /// Explicit label different from bound pattern name (`label name: Type`).
    Label(Spanned<String>),
    /// No prefix/alias: label is derived from simple variable pattern name.
    Implicit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub label: ParamLabel,
    pub pattern: Pattern,
    pub annotation: Option<Spanned<TypeAnnotation>>,
    pub default: Option<Expr>,
}

impl Param {
    pub fn is_borrowed(&self) -> bool {
        matches!(&self.label, ParamLabel::Borrow)
    }

    /// Returns the parameter name if the pattern is a simple variable.
    pub fn name(&self) -> Option<&str> {
        match &self.pattern.node {
            PatternKind::Var(name) => Some(name.as_str()),
            _ => None,
        }
    }

    /// Returns the effective call-site label when this parameter is labeled.
    pub fn effective_label(&self) -> Option<&str> {
        if self.is_borrowed() {
            return self.name();
        }
        match &self.label {
            ParamLabel::Positional => None,
            ParamLabel::Borrow => self.name(),
            ParamLabel::Label(label) => Some(label.node.as_str()),
            ParamLabel::Implicit => self.name(),
        }
    }

    /// Returns the span of the pattern.
    pub fn span(&self) -> Span {
        self.pattern.span
    }
}

/// A syntactic type annotation (not a semantic type — that's in `kea-types`).
#[derive(Debug, Clone, PartialEq)]
pub enum TypeAnnotation {
    Named(String),
    Applied(String, Vec<TypeAnnotation>),
    /// Row type annotation: `{ name: String, age: Int | r }`.
    Row {
        fields: Vec<(String, TypeAnnotation)>,
        rest: Option<String>,
    },
    EffectRow(EffectRowAnnotation),
    Tuple(Vec<TypeAnnotation>),
    Forall {
        type_vars: Vec<String>,
        ty: Box<TypeAnnotation>,
    },
    Function(Vec<TypeAnnotation>, Box<TypeAnnotation>),
    FunctionWithEffect(
        Vec<TypeAnnotation>,
        Spanned<EffectAnnotation>,
        Box<TypeAnnotation>,
    ),
    Optional(Box<TypeAnnotation>),
    /// Existential type: `any Show`, `any (Show, Eq)`, optionally with
    /// associated-type constraints (`any Iterable where Item = Int`).
    Existential {
        bounds: Vec<String>,
        associated_types: Vec<(String, TypeAnnotation)>,
    },
    /// Associated type projection: `Self.Source`, `Self.Message`.
    Projection {
        base: String,
        name: String,
    },
    /// Integer literal in a type-level position: `Decimal(18, 2)`, `FixedSizeList(Float, 768)`.
    /// The parser accepts these in any type application arg; the type checker validates
    /// whether the constructor actually accepts dimension parameters.
    DimLiteral(i64),
}

/// A syntactic effect annotation used on function signatures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EffectAnnotation {
    Pure,
    Volatile,
    Impure,
    Var(String),
    Row(EffectRowAnnotation),
}

/// Row-style effect annotation: `-[IO, Fail DbError | e]>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectRowAnnotation {
    pub effects: Vec<EffectRowItem>,
    pub rest: Option<String>,
}

/// One effect entry inside a row.
///
/// Examples:
/// - `IO` -> `{ name: "IO", payload: None }`
/// - `Fail DbError` -> `{ name: "Fail", payload: Some("DbError") }`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectRowItem {
    pub name: String,
    pub payload: Option<String>,
}

/// A syntactic kind annotation used in trait type-constructor parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KindAnnotation {
    Star,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Concat,  // ++  (Concatenable: String, List, Seq)
    Combine, // <>  (Monoid: generic combine)
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    In,
    NotIn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

// ---------------------------------------------------------------------------
// Top-level declarations
// ---------------------------------------------------------------------------

pub type Decl = Spanned<DeclKind>;

#[derive(Debug, Clone, PartialEq)]
pub enum DeclKind {
    /// Function definition.
    Function(FnDecl),

    /// Expression function: `expr f(x: Int) -> Int { x + 1 }`.
    /// Restricted body: no lambdas, lists, actors, I/O — compiles to MIR for all backends.
    ExprFn(ExprDecl),

    /// Type definition: `type Color = Red | Green | Blue`.
    TypeDef(TypeDef),

    /// Type alias: `alias UserId = Int`.
    AliasDecl(AliasDecl),

    /// Opaque type definition: `opaque UserId = Int`.
    OpaqueTypeDef(OpaqueTypeDef),

    /// Struct definition: `struct User { name: String, age: Int }`.
    RecordDef(RecordDef),

    /// Trait definition: `trait Additive { fn zero() -> Self  fn add(self, other: Self) -> Self }`.
    TraitDef(TraitDef),

    /// Effect declaration: `effect Log  fn log(msg: String) -> ()`.
    EffectDecl(EffectDecl),

    /// Implementation block: `Int as Additive ...`.
    ImplBlock(ImplBlock),

    /// Module import: `use Module.{name1, name2}`.
    Import(ImportDecl),

    /// Test declaration: `test "name" { ... }` or
    /// `test property "name" { ... }`.
    Test(TestDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TestDecl {
    pub name: Spanned<String>,
    pub body: Expr,
    pub is_property: bool,
    pub iterations: Option<usize>,
    pub tags: Vec<Spanned<String>>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub public: bool,
    pub name: Spanned<String>,
    pub doc: Option<String>,
    pub annotations: Vec<Annotation>,
    pub params: Vec<Param>,
    pub return_annotation: Option<Spanned<TypeAnnotation>>,
    pub effect_annotation: Option<Spanned<EffectAnnotation>>,
    pub body: Expr,
    pub span: Span,
    pub where_clause: Vec<TraitBound>,
}

impl FnDecl {
    /// Convert this function declaration to a `let name = |params| body` expression.
    pub fn to_let_expr(&self) -> Expr {
        let lambda = Spanned::new(
            ExprKind::Lambda {
                params: self.params.clone(),
                body: Box::new(self.body.clone()),
                return_annotation: self.return_annotation.clone(),
            },
            self.span,
        );
        let name_pattern = Spanned::new(PatternKind::Var(self.name.node.clone()), self.name.span);
        Spanned::new(
            ExprKind::Let {
                pattern: name_pattern,
                annotation: None,
                value: Box::new(lambda),
            },
            self.span,
        )
    }
}

/// An `expr` declaration: a function whose body is restricted to the MIR grammar.
/// Compiles to DataFusion (columnar), Cranelift (scalar JIT), and eventually MLIR (tensor).
///
/// Syntax: `expr f(x: Int, y: Int) -> Int { x + y }`
/// Same structure as `FnDecl` — the restriction is enforced by `validate_expr_body` after parsing.
#[derive(Debug, Clone, PartialEq)]
pub struct ExprDecl {
    pub public: bool,
    pub name: Spanned<String>,
    pub doc: Option<String>,
    pub annotations: Vec<Annotation>,
    pub params: Vec<Param>,
    pub return_annotation: Option<Spanned<TypeAnnotation>>,
    pub effect_annotation: Option<Spanned<EffectAnnotation>>,
    pub body: Expr,
    pub span: Span,
    pub where_clause: Vec<TraitBound>,
}

impl ExprDecl {
    /// Convert to a `let name = |params| body` expression, same as `FnDecl::to_let_expr`.
    /// Type-checking treats `expr` bodies the same as `fn` bodies — the MIR restriction
    /// is enforced separately by `validate_expr_body`.
    pub fn to_let_expr(&self) -> Expr {
        let lambda = Spanned::new(
            ExprKind::Lambda {
                params: self.params.clone(),
                body: Box::new(self.body.clone()),
                return_annotation: self.return_annotation.clone(),
            },
            self.span,
        );
        let name_pattern = Spanned::new(PatternKind::Var(self.name.node.clone()), self.name.span);
        Spanned::new(
            ExprKind::Let {
                pattern: name_pattern,
                annotation: None,
                value: Box::new(lambda),
            },
            self.span,
        )
    }
}

/// Variant of a sum type.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeVariant {
    pub annotations: Vec<Annotation>,
    pub name: Spanned<String>,
    pub fields: Vec<VariantField>,
    /// Optional GADT-style equality constraints: `where T = Int, U = Bool`.
    pub where_clause: Vec<VariantWhereItem>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantField {
    pub annotations: Vec<Annotation>,
    pub name: Option<Spanned<String>>,
    pub ty: Spanned<TypeAnnotation>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantWhereItem {
    pub type_var: Spanned<String>,
    pub ty: Spanned<TypeAnnotation>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDef {
    pub public: bool,
    pub name: Spanned<String>,
    pub doc: Option<String>,
    pub annotations: Vec<Annotation>,
    pub params: Vec<String>,
    pub variants: Vec<TypeVariant>,
    pub derives: Vec<Spanned<String>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AliasDecl {
    pub public: bool,
    pub name: Spanned<String>,
    pub doc: Option<String>,
    pub params: Vec<String>,
    pub target: Spanned<TypeAnnotation>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct OpaqueTypeDef {
    pub public: bool,
    pub name: Spanned<String>,
    pub doc: Option<String>,
    pub params: Vec<String>,
    pub target: Spanned<TypeAnnotation>,
    pub derives: Vec<Spanned<String>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordDef {
    pub public: bool,
    pub name: Spanned<String>,
    pub doc: Option<String>,
    pub annotations: Vec<Annotation>,
    pub params: Vec<String>,
    pub fields: Vec<(Spanned<String>, TypeAnnotation)>,
    /// Per-field annotations aligned with `fields` by index.
    pub field_annotations: Vec<Vec<Annotation>>,
    pub derives: Vec<Spanned<String>>,
}

/// A trait definition: `trait Orderable: Eq { fn compare(self, other: Self) -> Int }`.
#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    pub public: bool,
    pub name: Spanned<String>,
    pub doc: Option<String>,
    pub type_params: Vec<TraitTypeParam>,
    pub supertraits: Vec<Spanned<String>>,
    pub fundeps: Vec<FunctionalDependencyDecl>,
    pub associated_types: Vec<AssociatedTypeDecl>,
    pub methods: Vec<TraitMethod>,
}

/// A trait parameter with an explicit kind annotation.
#[derive(Debug, Clone, PartialEq)]
pub struct TraitTypeParam {
    pub name: Spanned<String>,
    pub kind: KindAnnotation,
}

/// A functional dependency declaration on a trait.
///
/// Example: `| C -> E`, `| (A, B) -> C`.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionalDependencyDecl {
    pub from: Vec<Spanned<String>>,
    pub to: Vec<Spanned<String>>,
}

/// An associated type declaration within a trait definition.
///
/// Examples: `type Source`, `type Message where Message: Sendable`, `type Error = String`
#[derive(Debug, Clone, PartialEq)]
pub struct AssociatedTypeDecl {
    pub name: Spanned<String>,
    pub constraints: Vec<Spanned<String>>,
    pub default: Option<Spanned<TypeAnnotation>>,
}

/// A method signature within a trait definition.
#[derive(Debug, Clone, PartialEq)]
pub struct TraitMethod {
    pub name: Spanned<String>,
    pub params: Vec<Param>,
    pub return_annotation: Option<Spanned<TypeAnnotation>>,
    pub effect_annotation: Option<Spanned<EffectAnnotation>>,
    pub where_clause: Vec<TraitBound>,
    pub default_body: Option<Expr>,
    pub doc: Option<String>,
    pub span: Span,
}

/// An effect declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct EffectDecl {
    pub public: bool,
    pub name: Spanned<String>,
    pub doc: Option<String>,
    pub type_params: Vec<String>,
    pub operations: Vec<EffectOperation>,
}

/// An operation signature inside an effect declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct EffectOperation {
    pub name: Spanned<String>,
    pub params: Vec<Param>,
    pub return_annotation: Spanned<TypeAnnotation>,
    pub doc: Option<String>,
    pub span: Span,
}

/// An implementation block: `Int as Additive ...`.
#[derive(Debug, Clone, PartialEq)]
pub struct ImplBlock {
    pub trait_name: Spanned<String>,
    pub type_name: Spanned<String>,
    /// Optional type parameters declared on the impl target, e.g. `List(t)`.
    pub type_params: Vec<Spanned<String>>,
    pub methods: Vec<FnDecl>,
    /// Associated control type for actors: `where Control = SignalType`.
    pub control_type: Option<Spanned<TypeAnnotation>>,
    /// Where clause on impl: `where Source = String, schema: Deserialize`.
    pub where_clause: Vec<WhereItem>,
}

/// Spawn configuration: `spawn <expr> with { mailbox_size: 100, ... }`.
#[derive(Debug, Clone, PartialEq)]
pub struct SpawnConfig {
    pub mailbox_size: Option<Expr>,
    pub supervision: Option<Expr>,
    pub max_restarts: Option<Expr>,
    pub call_timeout: Option<Expr>,
}

/// A trait bound: `T: Additive`.
#[derive(Debug, Clone, PartialEq)]
pub struct TraitBound {
    pub type_var: Spanned<String>,
    pub trait_name: Spanned<String>,
}

/// An item in an impl's where clause (or fn where clause in future).
#[derive(Debug, Clone, PartialEq)]
pub enum WhereItem {
    /// Trait bound: `T: Trait` or `schema: Deserialize`.
    TraitBound(TraitBound),
    /// Associated type assignment: `Source = String`.
    TypeAssignment {
        name: Spanned<String>,
        ty: Spanned<TypeAnnotation>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImportDecl {
    pub module: Spanned<String>,
    pub items: ImportItems,
    /// Optional alias: `use Module as Alias`
    pub alias: Option<Spanned<String>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ImportItems {
    /// `use Module` — qualified access only (`Module.member()`)
    Module,
    /// `use Module.{a, b}` — brings specific names into bare scope
    Named(Vec<Spanned<String>>),
}

/// A complete source file / module.
#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub declarations: Vec<Decl>,
    pub span: Span,
}

// ---------------------------------------------------------------------------
// Free variable analysis
// ---------------------------------------------------------------------------

/// Compute the set of free variable names in an expression.
///
/// A variable is "free" if it is referenced (`Var`) but not bound by an
/// enclosing `Let`, `Lambda`, or pattern match within the expression.
///
/// This is useful for closure capture analysis — determining which
/// environment bindings a function body actually depends on.
pub fn free_vars(expr: &Expr) -> std::collections::HashSet<String> {
    let mut free = std::collections::HashSet::new();
    let mut bound = std::collections::HashSet::new();
    collect_free_vars(&expr.node, &mut free, &mut bound);
    free
}

fn collect_free_vars(
    kind: &ExprKind,
    free: &mut std::collections::HashSet<String>,
    bound: &mut std::collections::HashSet<String>,
) {
    match kind {
        ExprKind::Var(name) => {
            if !bound.contains(name) {
                free.insert(name.clone());
            }
        }
        ExprKind::Lit(_) | ExprKind::None | ExprKind::Atom(_) => {}
        ExprKind::Let { pattern, value, .. } => {
            collect_free_vars(&value.node, free, bound);
            collect_pattern_bindings(&pattern.node, bound);
        }
        ExprKind::Lambda { params, body, .. } => {
            let mut inner_bound = bound.clone();
            for p in params {
                collect_pattern_bindings(&p.pattern.node, &mut inner_bound);
            }
            collect_free_vars(&body.node, free, &mut inner_bound);
        }
        ExprKind::Call { func, args } => {
            collect_free_vars(&func.node, free, bound);
            for a in args {
                collect_free_vars(&a.value.node, free, bound);
            }
        }
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_free_vars(&condition.node, free, bound);
            collect_free_vars(&then_branch.node, free, bound);
            if let Some(e) = else_branch {
                collect_free_vars(&e.node, free, bound);
            }
        }
        ExprKind::Case { scrutinee, arms } => {
            collect_free_vars(&scrutinee.node, free, bound);
            for arm in arms {
                let mut arm_bound = bound.clone();
                collect_pattern_bindings(&arm.pattern.node, &mut arm_bound);
                if let Some(ref guard) = arm.guard {
                    collect_free_vars(&guard.node, free, &mut arm_bound);
                }
                collect_free_vars(&arm.body.node, free, &mut arm_bound);
            }
        }
        ExprKind::Cond { arms } => {
            for arm in arms {
                collect_free_vars(&arm.condition.node, free, bound);
                collect_free_vars(&arm.body.node, free, bound);
            }
        }
        ExprKind::For(for_expr) => {
            let mut scoped_bound = bound.clone();
            for clause in &for_expr.clauses {
                match clause {
                    ForClause::Generator { pattern, source } => {
                        collect_free_vars(&source.node, free, &mut scoped_bound);
                        collect_pattern_bindings(&pattern.node, &mut scoped_bound);
                    }
                    ForClause::Guard(guard) => {
                        collect_free_vars(&guard.node, free, &mut scoped_bound);
                    }
                }
            }
            collect_free_vars(&for_expr.body.node, free, &mut scoped_bound);
        }
        ExprKind::Use(use_expr) => {
            collect_free_vars(&use_expr.rhs.node, free, bound);
        }
        ExprKind::Handle {
            expr,
            clauses,
            then_clause,
        } => {
            collect_free_vars(&expr.node, free, bound);
            for clause in clauses {
                let mut clause_bound = bound.clone();
                for arg in &clause.args {
                    collect_pattern_bindings(&arg.node, &mut clause_bound);
                }
                collect_free_vars(&clause.body.node, free, &mut clause_bound);
            }
            if let Some(then_expr) = then_clause {
                collect_free_vars(&then_expr.node, free, bound);
            }
        }
        ExprKind::Resume { value } => {
            collect_free_vars(&value.node, free, bound);
        }
        ExprKind::BinaryOp { left, right, .. } => {
            collect_free_vars(&left.node, free, bound);
            collect_free_vars(&right.node, free, bound);
        }
        ExprKind::UnaryOp { operand, .. } => {
            collect_free_vars(&operand.node, free, bound);
        }
        ExprKind::WhenGuard { body, condition } => {
            collect_free_vars(&body.node, free, bound);
            collect_free_vars(&condition.node, free, bound);
        }
        ExprKind::Range { start, end, .. } => {
            collect_free_vars(&start.node, free, bound);
            collect_free_vars(&end.node, free, bound);
        }
        ExprKind::As { expr, .. } => {
            collect_free_vars(&expr.node, free, bound);
        }
        ExprKind::Tuple(exprs) | ExprKind::List(exprs) => {
            for e in exprs {
                collect_free_vars(&e.node, free, bound);
            }
        }
        ExprKind::Record { fields, spread, .. } | ExprKind::AnonRecord { fields, spread } => {
            for (_, e) in fields {
                collect_free_vars(&e.node, free, bound);
            }
            if let Some(s) = spread {
                collect_free_vars(&s.node, free, bound);
            }
        }
        ExprKind::Update { base, fields } => {
            collect_free_vars(&base.node, free, bound);
            for (_, e) in fields {
                collect_free_vars(&e.node, free, bound);
            }
        }
        ExprKind::FieldAccess { expr, .. } => {
            collect_free_vars(&expr.node, free, bound);
        }
        ExprKind::Block(exprs) => {
            // Block introduces sequential let bindings
            let mut block_bound = bound.clone();
            for e in exprs {
                collect_free_vars(&e.node, free, &mut block_bound);
            }
        }
        ExprKind::Constructor { args, .. } => {
            for a in args {
                collect_free_vars(&a.value.node, free, bound);
            }
        }
        ExprKind::StringInterp(parts) => {
            for part in parts {
                if let StringInterpPart::Expr(e) = part {
                    collect_free_vars(&e.node, free, bound);
                }
            }
        }
        ExprKind::MapLiteral(pairs) => {
            for (k, v) in pairs {
                collect_free_vars(&k.node, free, bound);
                collect_free_vars(&v.node, free, bound);
            }
        }
        ExprKind::Spawn { value, .. } => {
            collect_free_vars(&value.node, free, bound);
        }
        ExprKind::Await { expr, .. } => {
            collect_free_vars(&expr.node, free, bound);
        }
        ExprKind::StreamBlock { body, .. } => {
            collect_free_vars(&body.node, free, bound);
        }
        ExprKind::Yield { value } => {
            collect_free_vars(&value.node, free, bound);
        }
        ExprKind::YieldFrom { source } => {
            collect_free_vars(&source.node, free, bound);
        }
        ExprKind::ActorSend { actor, args, .. } | ExprKind::ActorCall { actor, args, .. } => {
            collect_free_vars(&actor.node, free, bound);
            for a in args {
                collect_free_vars(&a.node, free, bound);
            }
        }
        ExprKind::ControlSend { actor, signal } => {
            collect_free_vars(&actor.node, free, bound);
            collect_free_vars(&signal.node, free, bound);
        }
        ExprKind::Wildcard => {}
    }
}

/// Collect variable names bound by a pattern.
/// Collect all variable names bound by a pattern into a set.
pub fn collect_pattern_bindings_pub(
    pattern: &PatternKind,
    bound: &mut std::collections::HashSet<String>,
) {
    collect_pattern_bindings(pattern, bound);
}

fn collect_pattern_bindings(pattern: &PatternKind, bound: &mut std::collections::HashSet<String>) {
    match pattern {
        PatternKind::Wildcard | PatternKind::Lit(_) => {}
        PatternKind::Var(name) => {
            bound.insert(name.clone());
        }
        PatternKind::Constructor { args, .. } => {
            for a in args {
                collect_pattern_bindings(&a.pattern.node, bound);
            }
        }
        PatternKind::Tuple(pats) => {
            for p in pats {
                collect_pattern_bindings(&p.node, bound);
            }
        }
        PatternKind::Record { fields, .. } | PatternKind::AnonRecord { fields, .. } => {
            for (_, p) in fields {
                collect_pattern_bindings(&p.node, bound);
            }
        }
        PatternKind::Or(alternatives) => {
            // All alternatives must bind the same names — collect from the first
            if let Some(first) = alternatives.first() {
                collect_pattern_bindings(&first.node, bound);
            }
        }
        PatternKind::As { pattern, name } => {
            bound.insert(name.node.clone());
            collect_pattern_bindings(&pattern.node, bound);
        }
        PatternKind::List { elements, rest } => {
            for p in elements {
                collect_pattern_bindings(&p.node, bound);
            }
            if let Some(rest_pat) = rest {
                collect_pattern_bindings(&rest_pat.node, bound);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn span_merge() {
        let file = FileId(0);
        let a = Span::new(file, 10, 20);
        let b = Span::new(file, 15, 30);
        let merged = a.merge(b);
        assert_eq!(merged.start, 10);
        assert_eq!(merged.end, 30);
    }

    #[test]
    fn spanned_map() {
        let s = Spanned::new(42, Span::new(FileId(0), 0, 1));
        let s2 = s.map(|n| n.to_string());
        assert_eq!(s2.node, "42");
    }

    fn mk(kind: ExprKind) -> Expr {
        Spanned::new(kind, Span::synthetic())
    }

    #[test]
    fn free_vars_literal() {
        let e = mk(ExprKind::Lit(Lit::Int(42)));
        assert!(free_vars(&e).is_empty());
    }

    #[test]
    fn free_vars_var() {
        let e = mk(ExprKind::Var("x".into()));
        assert_eq!(free_vars(&e), ["x".to_string()].into_iter().collect());
    }

    #[test]
    fn free_vars_lambda_binds_params() {
        // |x| x + y — x is bound, y is free
        let body = mk(ExprKind::BinaryOp {
            op: Spanned::new(BinOp::Add, Span::synthetic()),
            left: Box::new(mk(ExprKind::Var("x".into()))),
            right: Box::new(mk(ExprKind::Var("y".into()))),
        });
        let lambda = mk(ExprKind::Lambda {
            params: vec![Param {
                label: ParamLabel::Implicit,
                pattern: Spanned::new(PatternKind::Var("x".into()), Span::synthetic()),
                annotation: None,
                default: None,
            }],
            body: Box::new(body),
            return_annotation: None,
        });
        let fv = free_vars(&lambda);
        assert!(fv.contains("y"));
        assert!(!fv.contains("x"));
    }

    #[test]
    fn free_vars_let_binds() {
        // let x = 1; x + y — y is free, x is bound
        let block = mk(ExprKind::Block(vec![
            mk(ExprKind::Let {
                pattern: Spanned::new(PatternKind::Var("x".into()), Span::synthetic()),
                annotation: None,
                value: Box::new(mk(ExprKind::Lit(Lit::Int(1)))),
            }),
            mk(ExprKind::BinaryOp {
                op: Spanned::new(BinOp::Add, Span::synthetic()),
                left: Box::new(mk(ExprKind::Var("x".into()))),
                right: Box::new(mk(ExprKind::Var("y".into()))),
            }),
        ]));
        let fv = free_vars(&block);
        assert!(fv.contains("y"));
        assert!(!fv.contains("x"));
    }

    #[test]
    fn free_vars_pure_function_empty() {
        // |x| x * 2 — no free variables
        let body = mk(ExprKind::BinaryOp {
            op: Spanned::new(BinOp::Mul, Span::synthetic()),
            left: Box::new(mk(ExprKind::Var("x".into()))),
            right: Box::new(mk(ExprKind::Lit(Lit::Int(2)))),
        });
        let fv = free_vars(&body);
        // "x" is free in the body itself — but when used as lambda body with param "x",
        // the lambda's free_vars would exclude it. Here we test the raw body.
        assert_eq!(fv, ["x".to_string()].into_iter().collect());

        // Now wrap in lambda
        let lambda = mk(ExprKind::Lambda {
            params: vec![Param {
                label: ParamLabel::Implicit,
                pattern: Spanned::new(PatternKind::Var("x".into()), Span::synthetic()),
                annotation: None,
                default: None,
            }],
            body: Box::new(body.clone()),
            return_annotation: None,
        });
        assert!(free_vars(&lambda).is_empty());
    }

    #[test]
    fn free_vars_nested_lambda() {
        // |x| |y| x + y + z — z is free, x and y are bound
        let inner_body = mk(ExprKind::BinaryOp {
            op: Spanned::new(BinOp::Add, Span::synthetic()),
            left: Box::new(mk(ExprKind::BinaryOp {
                op: Spanned::new(BinOp::Add, Span::synthetic()),
                left: Box::new(mk(ExprKind::Var("x".into()))),
                right: Box::new(mk(ExprKind::Var("y".into()))),
            })),
            right: Box::new(mk(ExprKind::Var("z".into()))),
        });
        let inner_lambda = mk(ExprKind::Lambda {
            params: vec![Param {
                label: ParamLabel::Implicit,
                pattern: Spanned::new(PatternKind::Var("y".into()), Span::synthetic()),
                annotation: None,
                default: None,
            }],
            body: Box::new(inner_body),
            return_annotation: None,
        });
        let outer_lambda = mk(ExprKind::Lambda {
            params: vec![Param {
                label: ParamLabel::Implicit,
                pattern: Spanned::new(PatternKind::Var("x".into()), Span::synthetic()),
                annotation: None,
                default: None,
            }],
            body: Box::new(inner_lambda),
            return_annotation: None,
        });
        let fv = free_vars(&outer_lambda);
        assert_eq!(fv, ["z".to_string()].into_iter().collect());
    }

    #[test]
    fn free_vars_case_binds_pattern() {
        // case x { Some(v) -> v + y } — x and y are free, v is bound by pattern
        let arm_body = mk(ExprKind::BinaryOp {
            op: Spanned::new(BinOp::Add, Span::synthetic()),
            left: Box::new(mk(ExprKind::Var("v".into()))),
            right: Box::new(mk(ExprKind::Var("y".into()))),
        });
        let case_expr = mk(ExprKind::Case {
            scrutinee: Box::new(mk(ExprKind::Var("x".into()))),
            arms: vec![CaseArm {
                pattern: Spanned::new(
                    PatternKind::Constructor {
                        name: "Some".into(),
                        qualifier: None,
                        args: vec![ConstructorFieldPattern {
                            name: None,
                            pattern: Spanned::new(PatternKind::Var("v".into()), Span::synthetic()),
                        }],
                        rest: false,
                    },
                    Span::synthetic(),
                ),
                guard: None,
                body: arm_body,
            }],
        });
        let fv = free_vars(&case_expr);
        assert!(fv.contains("x"), "scrutinee is free");
        assert!(fv.contains("y"), "y in arm body is free");
        assert!(!fv.contains("v"), "v is bound by pattern");
    }

    #[test]
    fn free_vars_if_then_else() {
        // if cond then a else b — all three are free
        let ite = mk(ExprKind::If {
            condition: Box::new(mk(ExprKind::Var("cond".into()))),
            then_branch: Box::new(mk(ExprKind::Var("a".into()))),
            else_branch: Some(Box::new(mk(ExprKind::Var("b".into())))),
        });
        let fv = free_vars(&ite);
        assert_eq!(fv.len(), 3);
        assert!(fv.contains("cond"));
        assert!(fv.contains("a"));
        assert!(fv.contains("b"));
    }

    #[test]
    fn free_vars_block_sequential_binding() {
        // { let a = x; let b = a; b + y }
        // x and y are free, a and b are bound
        let block = mk(ExprKind::Block(vec![
            mk(ExprKind::Let {
                pattern: Spanned::new(PatternKind::Var("a".into()), Span::synthetic()),
                annotation: None,
                value: Box::new(mk(ExprKind::Var("x".into()))),
            }),
            mk(ExprKind::Let {
                pattern: Spanned::new(PatternKind::Var("b".into()), Span::synthetic()),
                annotation: None,
                value: Box::new(mk(ExprKind::Var("a".into()))),
            }),
            mk(ExprKind::BinaryOp {
                op: Spanned::new(BinOp::Add, Span::synthetic()),
                left: Box::new(mk(ExprKind::Var("b".into()))),
                right: Box::new(mk(ExprKind::Var("y".into()))),
            }),
        ]));
        let fv = free_vars(&block);
        assert!(fv.contains("x"), "x is free (let a = x)");
        assert!(fv.contains("y"), "y is free");
        assert!(!fv.contains("a"), "a is bound by let");
        assert!(!fv.contains("b"), "b is bound by let");
    }

    #[test]
    fn free_vars_string_interpolation() {
        // "hello ${name}" — name is free
        let interp = mk(ExprKind::StringInterp(vec![
            StringInterpPart::Literal("hello ".into()),
            StringInterpPart::Expr(Box::new(mk(ExprKind::Var("name".into())))),
        ]));
        let fv = free_vars(&interp);
        assert_eq!(fv, ["name".to_string()].into_iter().collect());
    }

    #[test]
    fn free_vars_call() {
        // f(x, y) — f, x, y are all free
        let call = mk(ExprKind::Call {
            func: Box::new(mk(ExprKind::Var("f".into()))),
            args: vec![
                Argument {
                    label: None,
                    value: mk(ExprKind::Var("x".into())),
                },
                Argument {
                    label: None,
                    value: mk(ExprKind::Var("y".into())),
                },
            ],
        });
        let fv = free_vars(&call);
        assert_eq!(fv.len(), 3);
        assert!(fv.contains("f"));
        assert!(fv.contains("x"));
        assert!(fv.contains("y"));
    }
}
