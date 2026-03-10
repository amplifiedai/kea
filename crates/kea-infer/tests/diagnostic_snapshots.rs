//! Snapshot tests for diagnostic output quality.
//!
//! Each test exercises one error category and snapshots the rendered diagnostic
//! message. This prevents diagnostic regression — any change to error output
//! requires a deliberate snapshot update.
//!
//! Invariant: no unification variables (`?t0`, `?r1`) may appear in any snapshot.

use std::fmt::Write;

use kea_ast::{FileId, Span};
use kea_diag::{Category, Diagnostic};
use kea_infer::{InferenceContext, Provenance, Reason};
use kea_types::{Label, RowType, Type};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

fn s() -> Span {
    Span::new(FileId(0), 0, 20)
}

fn prov(reason: Reason) -> Provenance {
    Provenance { span: s(), reason }
}

fn format_diagnostics(diags: &[Diagnostic]) -> String {
    let mut out = String::new();
    for (i, d) in diags.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        writeln!(&mut out, "{d}").unwrap();
    }
    out
}

/// Unify two closed rows and return the resulting diagnostics.
///
/// `InferenceContext::solve()` moves errors into the `Err` variant; we
/// collect them from there rather than from `ctx.errors()`.
fn row_errors(
    expected: Vec<(&str, Type)>,
    actual: Vec<(&str, Type)>,
    reason: Reason,
) -> Vec<Diagnostic> {
    let mut ctx = InferenceContext::new();
    let exp = RowType::closed(
        expected
            .into_iter()
            .map(|(l, t)| (Label::new(l), t))
            .collect(),
    );
    let act = RowType::closed(
        actual
            .into_iter()
            .map(|(l, t)| (Label::new(l), t))
            .collect(),
    );
    ctx.constrain_row_equal(exp, act, prov(reason));
    match ctx.solve() {
        Ok(()) => vec![],
        Err(e) => e.diagnostics().to_vec(),
    }
}

/// Unify two types and return the resulting diagnostics.
fn type_errors(expected: Type, actual: Type, reason: Reason) -> Vec<Diagnostic> {
    let mut ctx = InferenceContext::new();
    ctx.constrain_equal(expected, actual, prov(reason));
    match ctx.solve() {
        Ok(()) => vec![],
        Err(e) => e.diagnostics().to_vec(),
    }
}

// ---------------------------------------------------------------------------
// Category metadata snapshot — codes and descriptions must be stable
// ---------------------------------------------------------------------------

#[test]
fn snapshot_category_metadata() {
    let mut out = String::new();
    for cat in Category::all() {
        writeln!(&mut out, "{}: {} — {}", cat.code(), cat.as_str(), cat.description()).unwrap();
    }
    insta::assert_snapshot!("category_metadata", out);
}

// ---------------------------------------------------------------------------
// E0001 — TypeMismatch: return type annotation disagrees with body
// ---------------------------------------------------------------------------

#[test]
fn snapshot_e0001_type_mismatch() {
    let diags = type_errors(Type::Int, Type::String, Reason::ReturnType);
    insta::assert_snapshot!("e0001_type_mismatch", format_diagnostics(&diags));
}

// ---------------------------------------------------------------------------
// E0002 — MissingField: single field missing, nothing extra
// ---------------------------------------------------------------------------

#[test]
fn snapshot_e0002_missing_field() {
    let diags = row_errors(
        vec![("name", Type::String), ("age", Type::Int)],
        vec![("name", Type::String)],
        Reason::LetAnnotation,
    );
    insta::assert_snapshot!("e0002_missing_field", format_diagnostics(&diags));
}

// ---------------------------------------------------------------------------
// E0011 — ExtraField: single extra field, nothing missing
// ---------------------------------------------------------------------------

#[test]
fn snapshot_e0011_extra_field() {
    let diags = row_errors(
        vec![("name", Type::String)],
        vec![("name", Type::String), ("temp", Type::Int)],
        Reason::LetAnnotation,
    );
    insta::assert_snapshot!("e0011_extra_field", format_diagnostics(&diags));
}

// ---------------------------------------------------------------------------
// E0013 — RecordRowMismatch: both missing and extra fields in one message
// ---------------------------------------------------------------------------

#[test]
fn snapshot_e0013_record_row_mismatch() {
    // Expected: { x: Float, y: Float }  Actual: { name: String, x: Float }
    // → missing: y: Float,  extra: name: String
    let diags = row_errors(
        vec![("x", Type::Float), ("y", Type::Float)],
        vec![("name", Type::String), ("x", Type::Float)],
        Reason::LetAnnotation,
    );
    insta::assert_snapshot!("e0013_record_row_mismatch", format_diagnostics(&diags));
}

#[test]
fn snapshot_e0013_record_row_mismatch_function_arg() {
    // Record mismatch in a function argument context.
    let diags = row_errors(
        vec![("x", Type::Float), ("y", Type::Float)],
        vec![("name", Type::String), ("x", Type::Float)],
        Reason::FunctionArg { param_index: 0 },
    );
    insta::assert_snapshot!(
        "e0013_record_row_mismatch_fn_arg",
        format_diagnostics(&diags)
    );
}

// ---------------------------------------------------------------------------
// E0014 — EffectRowMismatch: body requires more effects than declared
// ---------------------------------------------------------------------------

#[test]
fn snapshot_e0014_effect_row_mismatch_pure_to_io_fail() {
    // Declared: pure (empty effect row). Body requires: Fail, IO.
    let diags = row_errors(
        vec![], // expected = declared (pure)
        vec![("Fail", Type::Unit), ("IO", Type::Unit)], // actual = body effects
        Reason::EffectRowAnnotation,
    );
    insta::assert_snapshot!(
        "e0014_effect_row_mismatch_pure_to_io_fail",
        format_diagnostics(&diags)
    );
}

#[test]
fn snapshot_e0014_effect_row_mismatch_io_to_io_net() {
    // Declared: [IO]. Body requires: [IO, Net].
    let diags = row_errors(
        vec![("IO", Type::Unit)], // declared
        vec![("IO", Type::Unit), ("Net", Type::Unit)], // body
        Reason::EffectRowAnnotation,
    );
    insta::assert_snapshot!(
        "e0014_effect_row_mismatch_io_to_io_net",
        format_diagnostics(&diags)
    );
}

#[test]
fn snapshot_e0014_effect_row_mismatch_custom_effect() {
    // Unknown effect gets the generic "performs the '...' effect" description.
    let diags = row_errors(
        vec![("IO", Type::Unit)],
        vec![("IO", Type::Unit), ("MyCustomEffect", Type::Unit)],
        Reason::EffectRowAnnotation,
    );
    insta::assert_snapshot!(
        "e0014_effect_row_mismatch_custom",
        format_diagnostics(&diags)
    );
}

// ---------------------------------------------------------------------------
// Invariant: no internal variables in any row-diff diagnostic
// ---------------------------------------------------------------------------

#[test]
fn no_internal_variables_in_record_row_diff() {
    let diags = row_errors(
        vec![("x", Type::Float), ("y", Type::Float)],
        vec![("name", Type::String), ("x", Type::Float)],
        Reason::LetAnnotation,
    );
    assert!(!diags.is_empty(), "expected at least one diagnostic");
    for d in &diags {
        let msg = &d.message;
        assert!(
            !msg.contains("t0") && !msg.contains("r0") && !msg.contains("TypeVar"),
            "internal variable leaked in message: {msg}"
        );
        if let Some(h) = &d.help {
            assert!(
                !h.contains("t0") && !h.contains("r0"),
                "internal variable leaked in help: {h}"
            );
        }
    }
}

#[test]
fn no_internal_variables_in_effect_row_diff() {
    let diags = row_errors(
        vec![],
        vec![("IO", Type::Unit), ("Net", Type::Unit)],
        Reason::EffectRowAnnotation,
    );
    assert!(!diags.is_empty(), "expected at least one diagnostic");
    for d in &diags {
        let msg = &d.message;
        assert!(
            !msg.contains("t0") && !msg.contains("r0"),
            "internal variable leaked in effect row message: {msg}"
        );
    }
}
