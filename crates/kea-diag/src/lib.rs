//! Error reporting and diagnostics for Kea.
//!
//! This crate provides structured diagnostics with source location tracking.
//! The key invariant from KERNEL §17: no unification variables in user-facing output.
//!
//! Diagnostics are created by other crates (for example, `kea-infer` and
//! `kea-syntax`) and
//! rendered here for display.

use serde::Serialize;
use std::collections::BTreeMap;
use std::fmt;
use std::sync::OnceLock;

// ---------------------------------------------------------------------------
// Diagnostic severity and categories
// ---------------------------------------------------------------------------

/// How severe a diagnostic is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Severity {
    Error,
    Warning,
    Info,
}

/// Broad category for diagnostics. Used for filtering and grouping.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Category {
    /// Type mismatch: expected X, got Y.
    TypeMismatch,
    /// Missing field in a record/row.
    MissingField,
    /// Duplicate field in a record/row.
    DuplicateField,
    /// Lacks constraint violation.
    LacksViolation,
    /// Undefined variable or name.
    UndefinedName,
    /// Syntax error.
    Syntax,
    /// Pattern matching: non-exhaustive case.
    NonExhaustive,
    /// Purity violation (impure function in ColumnExpr).
    PurityViolation,
    /// Arity mismatch in function call.
    ArityMismatch,
    /// Trait bound not satisfied.
    TraitBound,
    /// Extra field in a record/row.
    ExtraField,
    /// General type error.
    TypeError,
    /// Missing required type annotation on declaration boundaries.
    MissingAnnotation,
    /// Public module is missing a module-level doc block.
    MissingModuleDoc,
    /// Aggregated record row diff: missing and/or extra fields in one message.
    RecordRowMismatch,
    /// Aggregated effect row diff: unhandled and/or unnecessary effects in one message.
    EffectRowMismatch,
    /// An effect is required by the body but not declared in the function signature.
    UnhandledEffect,
    /// A handler clause covers an effect not performed by the handled expression.
    UnusedHandler,
    /// `catch` result type does not match the Fail error type.
    CatchTypeMismatch,
    /// Par callback has a non-empty effect row; Par requires pure callbacks.
    EffectfulParCallback,
}

impl Category {
    pub const ALL: [Category; 20] = [
        Category::TypeMismatch,
        Category::MissingField,
        Category::DuplicateField,
        Category::LacksViolation,
        Category::UndefinedName,
        Category::Syntax,
        Category::NonExhaustive,
        Category::PurityViolation,
        Category::ArityMismatch,
        Category::TraitBound,
        Category::ExtraField,
        Category::TypeError,
        Category::MissingAnnotation,
        Category::MissingModuleDoc,
        Category::RecordRowMismatch,
        Category::EffectRowMismatch,
        Category::UnhandledEffect,
        Category::UnusedHandler,
        Category::CatchTypeMismatch,
        Category::EffectfulParCallback,
    ];

    pub fn all() -> &'static [Category] {
        &Self::ALL
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Category::TypeMismatch => "type_mismatch",
            Category::MissingField => "missing_field",
            Category::DuplicateField => "duplicate_field",
            Category::LacksViolation => "lacks_violation",
            Category::UndefinedName => "undefined_name",
            Category::Syntax => "syntax",
            Category::NonExhaustive => "non_exhaustive",
            Category::PurityViolation => "purity_violation",
            Category::ArityMismatch => "arity_mismatch",
            Category::TraitBound => "trait_bound",
            Category::ExtraField => "extra_field",
            Category::TypeError => "type_error",
            Category::MissingAnnotation => "missing_annotation",
            Category::MissingModuleDoc => "missing_module_doc",
            Category::RecordRowMismatch => "record_row_mismatch",
            Category::EffectRowMismatch => "effect_row_mismatch",
            Category::UnhandledEffect => "unhandled_effect",
            Category::UnusedHandler => "unused_handler",
            Category::CatchTypeMismatch => "catch_type_mismatch",
            Category::EffectfulParCallback => "effectful_par_callback",
        }
    }

    pub fn code(self) -> &'static str {
        match self {
            Category::TypeMismatch => "E0001",
            Category::MissingField => "E0002",
            Category::DuplicateField => "E0003",
            Category::LacksViolation => "E0004",
            Category::UndefinedName => "E0005",
            Category::Syntax => "E0006",
            Category::NonExhaustive => "E0007",
            Category::PurityViolation => "E0008",
            Category::ArityMismatch => "E0009",
            Category::TraitBound => "E0010",
            Category::ExtraField => "E0011",
            Category::TypeError => "E0012",
            Category::MissingAnnotation => "E0801",
            Category::MissingModuleDoc => "W1001",
            Category::RecordRowMismatch => "E0013",
            Category::EffectRowMismatch => "E0014",
            Category::UnhandledEffect => "E0015",
            Category::UnusedHandler => "E0016",
            Category::CatchTypeMismatch => "E0017",
            Category::EffectfulParCallback => "E0018",
        }
    }

    pub fn description(self) -> &'static str {
        match self {
            Category::TypeMismatch => "Expression type does not match expected type.",
            Category::MissingField => "A required record or row field is missing.",
            Category::DuplicateField => "A record or row field is declared more than once.",
            Category::LacksViolation => "A row-polymorphism lacks constraint was violated.",
            Category::UndefinedName => "A referenced variable, function, or name is undefined.",
            Category::Syntax => "Source text does not parse as valid Kea syntax.",
            Category::NonExhaustive => "Pattern matching is missing one or more cases.",
            Category::PurityViolation => "An impure operation was used in a pure-only context.",
            Category::ArityMismatch => "A function was called with the wrong number of arguments.",
            Category::TraitBound => "A required trait bound is not satisfied for the given type.",
            Category::ExtraField => "A record or row contains a field not allowed in this context.",
            Category::TypeError => "General type checking error.",
            Category::MissingAnnotation => {
                "A required declaration-boundary type annotation is missing."
            }
            Category::MissingModuleDoc => {
                "A public module has no module-level doc block."
            }
            Category::RecordRowMismatch => {
                "Record fields do not match: the value has missing or extra fields."
            }
            Category::EffectRowMismatch => {
                "Function effect row does not match: body performs effects not in the signature."
            }
            Category::UnhandledEffect => {
                "An effect is required by the function body but not declared in the signature."
            }
            Category::UnusedHandler => {
                "A handler clause covers an effect the expression does not perform."
            }
            Category::CatchTypeMismatch => {
                "`catch` result type does not match the Fail error type."
            }
            Category::EffectfulParCallback => {
                "A callback passed to a Par operation has a non-empty effect row. \
                Par.map, Par.all2, and Par.all3 require pure callbacks (`fn(A) -> B`) \
                because they may execute on separate threads."
            }
        }
    }

    pub fn example_fix(self) -> &'static str {
        match self {
            Category::TypeMismatch => {
                "Adjust the expression or add a conversion to match expected type."
            }
            Category::MissingField => "Add the missing field or use an open record/row type.",
            Category::DuplicateField => "Remove or rename duplicated fields.",
            Category::LacksViolation => {
                "Avoid introducing the forbidden label for this row variable."
            }
            Category::UndefinedName => "Define/import the missing name or fix the spelling.",
            Category::Syntax => "Fix parser-reported syntax near the highlighted span.",
            Category::NonExhaustive => "Add a wildcard or the missing pattern arms.",
            Category::PurityViolation => {
                "Move the impure call out of pure context or use a pure alternative."
            }
            Category::ArityMismatch => "Call the function with its declared parameter count.",
            Category::TraitBound => {
                "Constrain the type, convert it, or implement the required trait."
            }
            Category::ExtraField => "Remove unknown fields or widen the expected row type.",
            Category::TypeError => {
                "Follow the labeled spans and help text to align involved types."
            }
            Category::MissingAnnotation => {
                "Add explicit parameter/return type annotations on named declarations."
            }
            Category::MissingModuleDoc => {
                "Add a `doc` block followed by a blank line at the top of the file, before any use statements."
            }
            Category::RecordRowMismatch => {
                "Add the missing fields and remove the extra fields to match the expected record type."
            }
            Category::EffectRowMismatch => {
                "Either add the required effects to the function signature or handle them in the body."
            }
            Category::UnhandledEffect => {
                "Add the effect to the function signature or wrap the body in a handler."
            }
            Category::UnusedHandler => {
                "Remove the handler clause for the effect that is not performed."
            }
            Category::CatchTypeMismatch => {
                "Adjust the catch binding type to match the actual Fail error type."
            }
            Category::EffectfulParCallback => {
                "Remove effects from the callback or extract the effectful code outside the Par.map call."
            }
        }
    }

    /// Reverse lookup: `"E0013"` → `Some(Category::RecordRowMismatch)`.
    pub fn from_code(code: &str) -> Option<Category> {
        Category::all().iter().copied().find(|c| c.code() == code)
    }
}

// ---------------------------------------------------------------------------
// Error registry — queryable metadata for every diagnostic code
// ---------------------------------------------------------------------------

/// Rich metadata for a single diagnostic code.
#[derive(Debug, Clone)]
pub struct ErrorEntry {
    /// Stable code, e.g. `"E0013"`.
    pub code: &'static str,
    pub category: Category,
    pub severity: Severity,
    /// Snake-case name, e.g. `"record_row_mismatch"`.
    pub name: &'static str,
    /// Short human title, e.g. `"Record fields do not match"`.
    pub title: &'static str,
    /// Paragraph-length prose explanation.
    pub description: &'static str,
    /// Triggering Kea source snippet (may be multi-line), or `None`.
    pub example: Option<&'static str>,
    /// Suggested fix (one sentence).
    pub fix: &'static str,
    /// Codes of related diagnostics.
    pub related: &'static [&'static str],
}

/// Global registry of all diagnostic codes.
pub struct ErrorRegistry {
    by_code: BTreeMap<&'static str, &'static ErrorEntry>,
    all: Vec<&'static ErrorEntry>,
}

impl ErrorRegistry {
    /// Returns the lazily-initialised global registry.
    pub fn global() -> &'static Self {
        static REGISTRY: OnceLock<ErrorRegistry> = OnceLock::new();
        REGISTRY.get_or_init(ErrorRegistry::build)
    }

    fn build() -> Self {
        let entries: &[&'static ErrorEntry] = &[
            &E0001, &E0002, &E0003, &E0004, &E0005, &E0006, &E0007, &E0008, &E0009,
            &E0010, &E0011, &E0012, &E0013, &E0014, &E0015, &E0016, &E0017, &E0018, &E0801,
            &W1001,
        ];
        let mut by_code = BTreeMap::new();
        for &entry in entries {
            by_code.insert(entry.code, entry);
        }
        Self {
            by_code,
            all: entries.to_vec(),
        }
    }

    /// Look up an entry by its code string (e.g. `"E0013"`).
    pub fn get(&self, code: &str) -> Option<&ErrorEntry> {
        self.by_code.get(code).copied()
    }

    /// All entries, in code order.
    pub fn all(&self) -> &[&ErrorEntry] {
        &self.all
    }
}

// Static error entries — one per diagnostic code.
// Keep descriptions factual; fix sentences imperative.

static E0001: ErrorEntry = ErrorEntry {
    code: "E0001",
    category: Category::TypeMismatch,
    severity: Severity::Error,
    name: "type_mismatch",
    title: "Type mismatch",
    description: "The type of an expression does not match what the context requires. \
        This can occur when passing the wrong argument type, returning the wrong type from a \
        function, or using a value in an incompatible context.",
    example: Some(
        "fn double(x: Int) -> Int\n  x * 2\n\nfn main()\n  double(\"hello\")  -- error[E0001]: expected Int, got String",
    ),
    fix: "Adjust the expression or add a conversion to produce the expected type.",
    related: &["E0013"],
};

static E0002: ErrorEntry = ErrorEntry {
    code: "E0002",
    category: Category::MissingField,
    severity: Severity::Error,
    name: "missing_field",
    title: "Missing record field",
    description: "A required field is absent from a record literal or the provided record \
        type is missing a field that the context requires.",
    example: Some(
        "fn get_y(p: { x: Float, y: Float }) -> Float\n  p.y\n\nfn main()\n  get_y({ x: 1.0 })  -- error[E0002]: missing field `y`",
    ),
    fix: "Add the missing field to the record literal or widen the expected type.",
    related: &["E0011", "E0013"],
};

static E0003: ErrorEntry = ErrorEntry {
    code: "E0003",
    category: Category::DuplicateField,
    severity: Severity::Error,
    name: "duplicate_field",
    title: "Duplicate record field",
    description: "The same field label appears more than once in a record literal or \
        type annotation.",
    example: Some(
        "let p = { x: 1.0, x: 2.0 }  -- error[E0003]: duplicate field `x`",
    ),
    fix: "Remove or rename the duplicate field.",
    related: &[],
};

static E0004: ErrorEntry = ErrorEntry {
    code: "E0004",
    category: Category::LacksViolation,
    severity: Severity::Error,
    name: "lacks_violation",
    title: "Row lacks-constraint violated",
    description: "A row-polymorphism `lacks` constraint was violated: a label that must \
        not appear in a row is present. This ensures safe row extension.",
    example: None,
    fix: "Avoid introducing the forbidden label in the row, or use a different row variable.",
    related: &[],
};

static E0005: ErrorEntry = ErrorEntry {
    code: "E0005",
    category: Category::UndefinedName,
    severity: Severity::Error,
    name: "undefined_name",
    title: "Undefined name",
    description: "A variable, function, or module member reference could not be resolved. \
        The name is either not in scope, misspelled, or not yet declared.",
    example: Some(
        "fn main()\n  print(greet())  -- error[E0005]: undefined name `greet`",
    ),
    fix: "Define or import the missing name, or fix the spelling.",
    related: &[],
};

static E0006: ErrorEntry = ErrorEntry {
    code: "E0006",
    category: Category::Syntax,
    severity: Severity::Error,
    name: "syntax",
    title: "Syntax error",
    description: "The source text could not be parsed as valid Kea syntax. This is \
        commonly caused by incorrect indentation, missing keywords, or mismatched delimiters.",
    example: None,
    fix: "Follow the highlighted span to locate and fix the syntax error.",
    related: &[],
};

static E0007: ErrorEntry = ErrorEntry {
    code: "E0007",
    category: Category::NonExhaustive,
    severity: Severity::Error,
    name: "non_exhaustive",
    title: "Non-exhaustive pattern match",
    description: "A `case` expression is missing one or more constructor patterns. \
        Every possible value of the scrutinee type must be covered.",
    example: Some(
        "fn describe(b: Bool) -> String\n  case b\n    True -> \"yes\"  -- error[E0007]: non-exhaustive, `False` not covered",
    ),
    fix: "Add the missing patterns or a wildcard `_` arm.",
    related: &[],
};

static E0008: ErrorEntry = ErrorEntry {
    code: "E0008",
    category: Category::PurityViolation,
    severity: Severity::Error,
    name: "purity_violation",
    title: "Purity violation",
    description: "An expression that performs effects was used where a pure expression \
        is required. Functions declared with `->` must have an empty effect row.",
    example: Some(
        "fn greet() -> String\n  IO.print(\"hi\")  -- error[E0008]: IO effect in pure function",
    ),
    fix: "Either declare the function with an effect row (`-[IO]>`) or remove the effectful call.",
    related: &["E0014", "E0015"],
};

static E0009: ErrorEntry = ErrorEntry {
    code: "E0009",
    category: Category::ArityMismatch,
    severity: Severity::Error,
    name: "arity_mismatch",
    title: "Arity mismatch",
    description: "A function was called with a different number of arguments than it \
        was declared to accept.",
    example: Some(
        "fn add(x: Int, y: Int) -> Int\n  x + y\n\nfn main()\n  add(1)  -- error[E0009]: expected 2 arguments, got 1",
    ),
    fix: "Call the function with exactly its declared number of parameters.",
    related: &[],
};

static E0010: ErrorEntry = ErrorEntry {
    code: "E0010",
    category: Category::TraitBound,
    severity: Severity::Error,
    name: "trait_bound",
    title: "Trait bound not satisfied",
    description: "A required trait is not implemented for the given type. Traits are \
        Kea's mechanism for principled overloading and generic programming.",
    example: Some(
        "fn show_it[A: Show](x: A) -> String\n  show(x)\n\nfn main()\n  show_it({ x: 1 })  -- error[E0010]: Show not satisfied for { x: Int }",
    ),
    fix: "Implement the required trait for the type, or constrain the type parameter.",
    related: &[],
};

static E0011: ErrorEntry = ErrorEntry {
    code: "E0011",
    category: Category::ExtraField,
    severity: Severity::Error,
    name: "extra_field",
    title: "Extra record field",
    description: "A record literal or value contains a field that is not expected by the \
        context type. The receiver type does not have that label.",
    example: Some(
        "fn get_x(p: { x: Float }) -> Float\n  p.x\n\nfn main()\n  get_x({ x: 1.0, y: 2.0 })  -- error[E0011]: extra field `y`",
    ),
    fix: "Remove the extra field or widen the expected type to include it.",
    related: &["E0002", "E0013"],
};

static E0012: ErrorEntry = ErrorEntry {
    code: "E0012",
    category: Category::TypeError,
    severity: Severity::Error,
    name: "type_error",
    title: "General type error",
    description: "A general type checking failure that does not fit a more specific \
        category. Follow the labeled spans in the diagnostic for context.",
    example: None,
    fix: "Follow the labeled spans and help text to align the involved types.",
    related: &["E0001"],
};

static E0013: ErrorEntry = ErrorEntry {
    code: "E0013",
    category: Category::RecordRowMismatch,
    severity: Severity::Error,
    name: "record_row_mismatch",
    title: "Record fields do not match",
    description: "A record value is missing required fields and/or contains extra fields \
        that the expected type does not allow. This is an aggregated diff covering both \
        missing and extra fields in a single message.",
    example: Some(
        "fn get_y(p: { x: Float, y: Float }) -> Float\n  p.y\n\nfn main()\n  get_y({ x: 1.0, name: \"pt\" })  -- error[E0013]: missing y: Float, extra name: String",
    ),
    fix: "Add the missing fields and remove the extra fields to match the expected record type.",
    related: &["E0002", "E0011"],
};

static E0014: ErrorEntry = ErrorEntry {
    code: "E0014",
    category: Category::EffectRowMismatch,
    severity: Severity::Error,
    name: "effect_row_mismatch",
    title: "Function effects do not match",
    description: "The effect row inferred from the function body does not match the \
        declared effect signature. The body performs effects that are not in the signature, \
        or the signature declares effects the body does not perform.",
    example: Some(
        "fn process(data: String) -> String\n  IO.print(data)  -- error[E0014]: body requires IO, signature is pure",
    ),
    fix: "Either add the required effects to the function signature or handle them in the body.",
    related: &["E0015", "E0016", "E0008"],
};

static E0015: ErrorEntry = ErrorEntry {
    code: "E0015",
    category: Category::UnhandledEffect,
    severity: Severity::Error,
    name: "unhandled_effect",
    title: "Unhandled effect",
    description: "An effect is performed by the function body but is neither declared in \
        the function's effect signature nor handled by a surrounding `handle` block.",
    example: Some(
        "fn fetch() -> String\n  Http.get(\"http://example.com\")  -- error[E0015]: Net effect not in signature",
    ),
    fix: "Add the effect to the function signature or wrap the effectful code in a handler.",
    related: &["E0014", "E0008"],
};

static E0016: ErrorEntry = ErrorEntry {
    code: "E0016",
    category: Category::UnusedHandler,
    severity: Severity::Error,
    name: "unused_handler",
    title: "Unnecessary effect handler",
    description: "A handler clause covers an effect that the handled expression does not \
        perform. This is detected conservatively: the diagnostic only fires when there is \
        positive evidence that the effect is absent (a closed effect row, or an open row \
        whose concrete fields do not include the target effect).",
    example: Some(
        "pub fn body() -[Log]> Int\n  Log.log(7)\n  42\n\nfn main()\n  handle body()\n    State.get() -> resume 0   -- error[E0016]: State is not performed by body",
    ),
    fix: "Remove the handler clause for the effect that is not performed by the expression.",
    related: &["E0014"],
};

static E0017: ErrorEntry = ErrorEntry {
    code: "E0017",
    category: Category::CatchTypeMismatch,
    severity: Severity::Error,
    name: "catch_type_mismatch",
    title: "Catch type mismatch",
    description: "`catch` converts a `Fail E` effect into a `Result T E` value. This \
        error fires when the `Fail` error type does not match the `Result` error type \
        declared at the binding site.",
    example: None,
    fix: "Adjust the catch binding type annotation to match the actual Fail error type.",
    related: &["E0014"],
};

static E0018: ErrorEntry = ErrorEntry {
    code: "E0018",
    category: Category::EffectfulParCallback,
    severity: Severity::Error,
    name: "effectful_par_callback",
    title: "Par callback must be pure",
    description: "A callback passed to `Par.map`, `Par.all2`, or `Par.all3` has a non-empty \
        effect row. Par operations may run callbacks on separate threads, so callbacks must be \
        pure (`fn(A) -> B`). An effectful callback (`fn(A) -[E]> B`) is a different type and \
        is caught at compile time.",
    example: Some(
        "Par.map(xs, fn(x: Int) -[IO]> Int\n  IO.println(show(x))\n  x)\n-- error[E0018]: Par callback must be pure\n--   got fn(Int) -[IO]> Int, expected fn(Int) -> Int",
    ),
    fix: "Remove effects from the callback or extract the effectful code outside the Par.map call.",
    related: &["E0014", "E0008"],
};

static E0801: ErrorEntry = ErrorEntry {
    code: "E0801",
    category: Category::MissingAnnotation,
    severity: Severity::Error,
    name: "missing_annotation",
    title: "Missing type annotation",
    description: "A named function declaration at module or struct level is missing an \
        explicit type annotation on its parameters or return type. Kea requires explicit \
        annotations at declaration boundaries for readability and reliable error messages.",
    example: Some(
        "fn greet(name)  -- error[E0801]: parameter `name` lacks a type annotation\n  IO.print(name)",
    ),
    fix: "Add explicit parameter and return type annotations to the declaration.",
    related: &[],
};

static W1001: ErrorEntry = ErrorEntry {
    code: "W1001",
    category: Category::MissingModuleDoc,
    severity: Severity::Warning,
    name: "missing_module_doc",
    title: "Missing module doc block",
    description: "A public module (file) does not have a module-level documentation \
        block. Kea enforces documentation on public modules to support `kea doc` and \
        tooling consumers.",
    example: Some(
        "-- missing doc block at top of file\npub fn greet() -[IO]> Unit\n  IO.print(\"hello\")",
    ),
    fix: "Add a `doc` block followed by a blank line at the top of the file, before any `use` statements.",
    related: &[],
};

// ---------------------------------------------------------------------------
// Source locations (independent of kea-ast's Span)
// ---------------------------------------------------------------------------

/// A source location for diagnostics.
///
/// Uses byte offsets. Callers convert from `kea-ast` spans to this type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub struct SourceLocation {
    pub file_id: u32,
    pub start: u32,
    pub end: u32,
}

// ---------------------------------------------------------------------------
// Diagnostic
// ---------------------------------------------------------------------------

/// A structured diagnostic message.
///
/// Every diagnostic carries enough context to produce an actionable error
/// message without exposing internal compiler state (KERNEL §17).
#[derive(Debug, Clone, Serialize)]
pub struct Diagnostic {
    /// Stable diagnostic code (e.g. E0001).
    pub code: Option<String>,
    pub severity: Severity,
    pub category: Category,
    /// Primary message: what went wrong.
    pub message: String,
    /// Where it went wrong.
    pub location: Option<SourceLocation>,
    /// Additional labeled spans (e.g., "expected type came from here").
    pub labels: Vec<DiagLabel>,
    /// Suggested fix, if any.
    pub help: Option<String>,
}

/// A labeled source span within a diagnostic.
#[derive(Debug, Clone, Serialize)]
pub struct DiagLabel {
    pub location: SourceLocation,
    pub message: String,
}

impl Diagnostic {
    pub fn error(category: Category, message: impl Into<String>) -> Self {
        Self {
            code: Some(category.code().to_string()),
            severity: Severity::Error,
            category,
            message: message.into(),
            location: None,
            labels: Vec::new(),
            help: None,
        }
    }

    pub fn warning(category: Category, message: impl Into<String>) -> Self {
        Self {
            code: Some(category.code().to_string()),
            severity: Severity::Warning,
            category,
            message: message.into(),
            location: None,
            labels: Vec::new(),
            help: None,
        }
    }

    pub fn at(mut self, location: SourceLocation) -> Self {
        self.location = Some(location);
        self
    }

    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }

    pub fn with_label(mut self, location: SourceLocation, message: impl Into<String>) -> Self {
        self.labels.push(DiagLabel {
            location,
            message: message.into(),
        });
        self
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Info => "info",
        };
        if let Some(code) = &self.code {
            write!(f, "{prefix}[{code}]: {}", self.message)?;
        } else {
            write!(f, "{prefix}: {}", self.message)?;
        }
        if let Some(help) = &self.help {
            write!(f, "\n  help: {help}")?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Error type for crates that produce diagnostics
// ---------------------------------------------------------------------------

/// Error type wrapping one or more diagnostics.
#[derive(Debug, Clone, thiserror::Error)]
#[error("{}", .0.first().map(|d| d.to_string()).unwrap_or_default())]
pub struct DiagnosticError(pub Vec<Diagnostic>);

impl DiagnosticError {
    pub fn single(diag: Diagnostic) -> Self {
        Self(vec![diag])
    }

    pub fn multiple(diags: Vec<Diagnostic>) -> Self {
        Self(diags)
    }

    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostic_builder() {
        let loc = SourceLocation {
            file_id: 0,
            start: 10,
            end: 20,
        };
        let diag = Diagnostic::error(Category::TypeMismatch, "Expected Int, got String")
            .at(loc)
            .with_help("Use `int(x)` to convert");

        assert_eq!(diag.severity, Severity::Error);
        assert_eq!(diag.code.as_deref(), Some("E0001"));
        assert_eq!(diag.category, Category::TypeMismatch);
        assert!(diag.message.contains("Expected Int"));
        assert!(diag.help.unwrap().contains("int(x)"));
    }

    #[test]
    fn diagnostic_display() {
        let diag = Diagnostic::error(Category::TypeMismatch, "Expected Int, got String");
        let s = format!("{diag}");
        assert!(s.starts_with("error[E0001]: Expected Int"));
    }

    #[test]
    fn category_metadata_is_stable_and_unique() {
        let mut codes = std::collections::BTreeSet::new();
        for cat in Category::all() {
            assert!(!cat.as_str().is_empty());
            assert!(!cat.description().is_empty());
            assert!(!cat.example_fix().is_empty());
            assert!(
                codes.insert(cat.code()),
                "duplicate diagnostic code detected: {}",
                cat.code()
            );
        }
    }

    #[test]
    fn category_from_code_round_trips() {
        for cat in Category::all() {
            let code = cat.code();
            let found = Category::from_code(code);
            assert_eq!(
                found,
                Some(*cat),
                "from_code({code}) should return {cat:?}"
            );
        }
        assert_eq!(Category::from_code("E9999"), None);
    }

    #[test]
    fn error_registry_covers_all_codes() {
        let registry = ErrorRegistry::global();
        // Every category code must be in the registry.
        for cat in Category::all() {
            let entry = registry.get(cat.code());
            assert!(
                entry.is_some(),
                "ErrorRegistry missing entry for {}",
                cat.code()
            );
            let entry = entry.unwrap();
            assert_eq!(entry.category, *cat);
            assert!(!entry.name.is_empty());
            assert!(!entry.title.is_empty());
            assert!(!entry.description.is_empty());
            assert!(!entry.fix.is_empty());
        }
        // all() length matches.
        assert_eq!(registry.all().len(), Category::ALL.len());
    }
}
