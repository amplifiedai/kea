//! Error reporting and diagnostics for Kea.
//!
//! This crate provides structured diagnostics with source location tracking.
//! The key invariant from KERNEL §17: no unification variables in user-facing output.
//!
//! Diagnostics are created by other crates (for example, `kea-infer` and
//! `kea-syntax`) and
//! rendered here for display.

use std::fmt;

// ---------------------------------------------------------------------------
// Diagnostic severity and categories
// ---------------------------------------------------------------------------

/// How severe a diagnostic is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Severity {
    Error,
    Warning,
    Info,
}

/// Broad category for diagnostics. Used for filtering and grouping.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
}

impl Category {
    pub const ALL: [Category; 13] = [
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
        }
    }
}

// ---------------------------------------------------------------------------
// Source locations (independent of kea-ast's Span)
// ---------------------------------------------------------------------------

/// A source location for diagnostics.
///
/// Uses byte offsets. Callers convert from `kea-ast` spans to this type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
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
}
