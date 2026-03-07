//! Exhaustiveness checking for case expressions.
//!
//! After type inference resolves the scrutinee type, this module checks
//! whether all constructors are covered by the case arms' patterns.
//! For finite types (Bool, sum types including Option and Result) it checks constructor coverage.
//! For infinite types (Int, Float, String) it requires a wildcard or
//! variable pattern.

use kea_ast::PatternKind;
use kea_types::{RowType, Type};

use crate::{
    Unifier,
    typeck::{RecordRegistry, SumTypeRegistry, instantiate_record_row, instantiate_sum_variants},
};

/// Check whether a set of patterns exhaustively covers the scrutinee type.
///
/// Returns a list of missing constructors/patterns. Empty means exhaustive.
pub fn check_exhaustiveness(
    scrutinee_ty: &Type,
    patterns: &[&kea_ast::Pattern],
    unifier: &Unifier,
    records: &RecordRegistry,
    sum_types: &SumTypeRegistry,
) -> Vec<String> {
    let resolved = unifier.substitution.apply(scrutinee_ty);

    // Flatten Or-patterns and As-patterns for exhaustiveness analysis
    let flat = flatten_patterns(patterns);
    let patterns = &flat[..];

    // If any pattern is a wildcard or variable, it covers everything
    if patterns
        .iter()
        .any(|p| matches!(p.node, PatternKind::Wildcard | PatternKind::Var(_)))
    {
        return vec![];
    }

    match &resolved {
        Type::Bool => check_bool(patterns),
        // Stdlib List: has Nil/Cons variants — needs [] and [_, .._] patterns
        // Only route to check_list for the actual stdlib List, not user-defined types named "List"
        Type::Sum(st) if st.name == "List" => {
            // Verify the registry confirms this is the stdlib List (has Nil/Cons).
            let variants = instantiate_sum_variants(st, sum_types)
                .unwrap_or_default();
            if variants.iter().any(|(v, _)| v == "Nil")
                && variants.iter().any(|(v, _)| v == "Cons")
            {
                check_list(patterns)
            } else {
                check_sum_type_from_variants(&variants, patterns)
            }
        }
        // Infinite types: must have wildcard/var (already checked above)
        Type::Int | Type::Float | Type::String => {
            vec!["_".to_string()]
        }
        // Unit: only one constructor ()
        Type::Unit => {
            if patterns
                .iter()
                .any(|p| matches!(p.node, PatternKind::Lit(kea_ast::Lit::Unit)))
            {
                vec![]
            } else {
                vec!["()".to_string()]
            }
        }
        // Sum types: check variant coverage via registry.
        Type::Sum(st) => {
            let variants = instantiate_sum_variants(st, sum_types).unwrap_or_default();
            check_sum_type_from_variants(&variants, patterns)
        }
        // Opaque types behave like a single-constructor nominal wrapper.
        Type::Opaque { name, .. } => check_opaque_type(name, patterns),
        // Other types: require at least one irrefutable structural pattern
        // or an explicit catch-all.
        _ => {
            if patterns
                .iter()
                .any(|p| pattern_irrefutable_for_type(p, &resolved, Some(records), sum_types))
            {
                vec![]
            } else {
                vec!["_".to_string()]
            }
        }
    }
}

fn check_bool(patterns: &[&kea_ast::Pattern]) -> Vec<String> {
    let mut has_true = false;
    let mut has_false = false;

    for p in patterns {
        match &p.node {
            PatternKind::Lit(kea_ast::Lit::Bool(true)) => has_true = true,
            PatternKind::Lit(kea_ast::Lit::Bool(false)) => has_false = true,
            PatternKind::Wildcard | PatternKind::Var(_) => return vec![],
            _ => {}
        }
    }

    let mut missing = vec![];
    if !has_true {
        missing.push("true".to_string());
    }
    if !has_false {
        missing.push("false".to_string());
    }
    missing
}

fn check_list(patterns: &[&kea_ast::Pattern]) -> Vec<String> {
    let mut has_empty = false;
    let mut has_nonempty_rest = false; // [_, .._] covers all non-empty lists

    for p in patterns {
        match &p.node {
            PatternKind::List { elements, rest } => {
                if elements.is_empty() && rest.is_none() {
                    // [] — covers empty list
                    has_empty = true;
                } else if rest.is_some() {
                    // [_, ..rest] — covers all lists of length >= elements.len()
                    if elements.is_empty() {
                        // [..rest] — covers everything (including empty)
                        has_empty = true;
                        has_nonempty_rest = true;
                    } else {
                        // [h, ..t] covers all non-empty
                        has_nonempty_rest = true;
                    }
                }
                // Fixed-length like [x] or [x, y] don't cover all non-empty
            }
            // Constructor-style list patterns: Nil/Cons from stdlib definitions or derive impls
            PatternKind::Constructor { name, args, .. } if name == "Nil" && args.is_empty() => {
                has_empty = true;
            }
            PatternKind::Constructor { name, .. } if name == "Cons" => {
                has_nonempty_rest = true;
            }
            PatternKind::Wildcard | PatternKind::Var(_) => return vec![],
            _ => {}
        }
    }

    let mut missing = vec![];
    if !has_empty {
        missing.push("[]".to_string());
    }
    if !has_nonempty_rest {
        missing.push("[_, .._]".to_string());
    }
    missing
}

fn check_sum_type_from_variants(
    variants: &[(String, Vec<kea_types::Type>)],
    patterns: &[&kea_ast::Pattern],
) -> Vec<String> {
    let mut covered = std::collections::BTreeSet::new();

    for p in patterns {
        match &p.node {
            PatternKind::Constructor { name, .. } => {
                covered.insert(name.as_str());
            }
            PatternKind::Wildcard | PatternKind::Var(_) => return vec![],
            _ => {}
        }
    }

    variants
        .iter()
        .filter(|(name, _)| !covered.contains(name.as_str()))
        .map(|(name, fields)| {
            if fields.is_empty() {
                name.clone()
            } else {
                format!("{}({})", name, vec!["_"; fields.len()].join(", "))
            }
        })
        .collect()
}

fn check_opaque_type(name: &str, patterns: &[&kea_ast::Pattern]) -> Vec<String> {
    for p in patterns {
        match &p.node {
            PatternKind::Constructor { name: ctor, .. } if ctor == name => return vec![],
            PatternKind::Wildcard | PatternKind::Var(_) => return vec![],
            _ => {}
        }
    }
    vec![format!("{name}(...)")]
}

/// Check whether a pattern is irrefutable for a given type.
///
/// Irrefutable patterns always match. Tuples, records, and wildcards/vars are
/// irrefutable. Sum type constructors are irrefutable only for single-variant
/// types (newtypes). Used to validate `let` destructuring patterns.
pub fn is_irrefutable(
    pattern: &kea_ast::Pattern,
    ty: &Type,
    sum_types: &SumTypeRegistry,
) -> bool {
    // is_irrefutable doesn't need the record registry since record field
    // irrefutability only depends on the row structure, which we look up
    // from the anonymous row side.  For full nominal accuracy we'd pass
    // records here too, but the existing call sites only need the sum check.
    pattern_irrefutable_for_type(pattern, ty, None, sum_types)
}

fn pattern_irrefutable_for_type(
    pattern: &kea_ast::Pattern,
    ty: &Type,
    records: Option<&RecordRegistry>,
    sum_types: &SumTypeRegistry,
) -> bool {
    match &pattern.node {
        PatternKind::Wildcard | PatternKind::Var(_) => true,
        PatternKind::Tuple(pats) => {
            if let Type::Tuple(elems) = ty {
                pats.len() == elems.len()
                    && pats
                        .iter()
                        .zip(elems)
                        .all(|(p, elem_ty)| pattern_irrefutable_for_type(p, elem_ty, records, sum_types))
            } else {
                false
            }
        }
        PatternKind::Record { name, fields, rest } => {
            if let Type::Record(rt) = ty {
                if &rt.name != name {
                    return false;
                }
                let row = records
                    .and_then(|reg| instantiate_record_row(rt, reg))
                    .unwrap_or_else(RowType::empty_closed);
                row_pattern_irrefutable(fields, *rest, &row, records, sum_types)
            } else {
                false
            }
        }
        PatternKind::AnonRecord { fields, rest } => match ty {
            Type::AnonRecord(row) => row_pattern_irrefutable(fields, *rest, row, records, sum_types),
            Type::Record(rt) => {
                let row = records
                    .and_then(|reg| instantiate_record_row(rt, reg))
                    .unwrap_or_else(RowType::empty_closed);
                row_pattern_irrefutable(fields, *rest, &row, records, sum_types)
            }
            _ => false,
        },
        PatternKind::Lit(kea_ast::Lit::Unit) => matches!(ty, Type::Unit),
        PatternKind::Constructor {
            name, args, rest, ..
        } => {
            if let Type::Opaque {
                name: opaque_name, ..
            } = ty
            {
                return name == opaque_name && !rest && args.len() == 1 && args[0].name.is_none();
            }
            if let Type::Sum(st) = ty {
                let variants = instantiate_sum_variants(st, sum_types).unwrap_or_default();
                if variants.len() != 1 {
                    return false;
                }
                if let Some((only_name, field_types)) = variants.first() {
                    if only_name != name {
                        return false;
                    }
                    if args.iter().any(|arg| arg.name.is_some()) {
                        return false;
                    }
                    if *rest {
                        if args.len() > field_types.len() {
                            return false;
                        }
                    } else if args.len() != field_types.len() {
                        return false;
                    }
                    return args
                        .iter()
                        .zip(field_types)
                        .all(|(p, field_ty)| pattern_irrefutable_for_type(&p.pattern, field_ty, records, sum_types));
                }
            }
            false
        }
        // List patterns are always refutable — can't know length statically
        PatternKind::List { .. } => false,
        PatternKind::As { pattern: inner, .. } => pattern_irrefutable_for_type(inner, ty, records, sum_types),
        PatternKind::Or(alternatives) => alternatives
            .iter()
            .any(|alt| pattern_irrefutable_for_type(alt, ty, records, sum_types)),
        _ => false,
    }
}

/// Flatten patterns: unwrap As-patterns, expand Or-patterns into individual patterns.
fn flatten_patterns<'a>(patterns: &[&'a kea_ast::Pattern]) -> Vec<&'a kea_ast::Pattern> {
    let mut out = Vec::new();
    for p in patterns {
        match &p.node {
            PatternKind::As { pattern: inner, .. } => {
                out.extend(flatten_patterns(&[inner]));
            }
            PatternKind::Or(alternatives) => {
                let refs: Vec<&kea_ast::Pattern> = alternatives.iter().collect();
                out.extend(flatten_patterns(&refs));
            }
            _ => out.push(p),
        }
    }
    out
}

fn row_pattern_irrefutable(
    fields: &[(String, kea_ast::Pattern)],
    rest: bool,
    row: &RowType,
    records: Option<&RecordRegistry>,
    sum_types: &SumTypeRegistry,
) -> bool {
    let required_fields = &row.fields;
    let field_map = fields
        .iter()
        .map(|(name, pat)| (name.as_str(), pat))
        .collect::<std::collections::BTreeMap<_, _>>();

    // Every field in the pattern must exist on the row and be irrefutable
    // for that field type.
    for (name, pat) in field_map {
        let Some((_, field_ty)) = required_fields
            .iter()
            .find(|(label, _)| label.as_str() == name)
        else {
            return false;
        };
        if !pattern_irrefutable_for_type(pat, field_ty, records, sum_types) {
            return false;
        }
    }

    // Closed record patterns must list every row field.
    if !rest {
        fields.len() == required_fields.len()
    } else {
        true
    }
}
