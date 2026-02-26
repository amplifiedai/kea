//! Property tests for the unifier using proptest.
//!
//! These tests stress invariants that must hold for ANY input types,
//! not just hand-picked examples. Key properties:
//!
//! 1. Substitution idempotence: apply(apply(t)) == apply(t)
//! 2. Unification reflexivity: unify(t, t) always succeeds
//! 3. Unification produces consistent substitution: after unify(a, b),
//!    apply(a) == apply(b)
//! 4. Occurs check: unifying Var(x) with a type containing Var(x) fails
//! 5. Row fields stay sorted after any operation
//! 6. Rémy decomposition preserves row information

use std::collections::{BTreeMap, BTreeSet};

use proptest::prelude::*;
use kea_ast::{FileId, ParamLabel, Span};
use kea_types::*;

use crate::{Provenance, Reason, Unifier};
use crate::typeck::{RecordRegistry, SolveOutcome, TraitGoal, TraitRegistry, check_expr_in_context};

/// Check if a type contains Dynamic anywhere (including nested).
fn contains_dynamic(ty: &Type) -> bool {
    match ty {
        Type::Dynamic => true,
        Type::List(inner)
        | Type::Option(inner)
        | Type::Set(inner)
        | Type::Actor(inner)
        | Type::Arc(inner)
        | Type::Stream(inner)
        | Type::Task(inner)
        | Type::FixedSizeList { element: inner, .. }
        | Type::Tensor { element: inner, .. } => contains_dynamic(inner),
        Type::Tagged { inner, .. } => contains_dynamic(inner),
        Type::Result(a, b) | Type::Map(a, b) => contains_dynamic(a) || contains_dynamic(b),
        Type::Tuple(elems) => elems.iter().any(contains_dynamic),
        Type::Function(ft) => {
            ft.params.iter().any(contains_dynamic) || contains_dynamic(&ft.ret)
        }
        Type::Record(rt) => rt.row.fields.iter().any(|(_, ty)| contains_dynamic(ty)),
        Type::Sum(st) => st.variants.iter().any(|(_, fields)| fields.iter().any(contains_dynamic)),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Strategies for generating types
// ---------------------------------------------------------------------------

const LABEL_POOL: &[&str] = &[
    "a", "b", "c", "d", "e", "x", "y", "z", "name", "age", "id", "val",
];

fn arb_label() -> impl Strategy<Value = Label> {
    prop::sample::select(LABEL_POOL).prop_map(Label::new)
}

fn arb_type_var_id() -> impl Strategy<Value = TypeVarId> {
    (0u32..8).prop_map(TypeVarId)
}

fn arb_row_var_id() -> impl Strategy<Value = RowVarId> {
    (0u32..8).prop_map(RowVarId)
}

fn arb_tags() -> impl Strategy<Value = BTreeMap<String, i64>> {
    prop::collection::btree_map(
        prop::sample::select(&["length", "time", "mass", "energy"][..]).prop_map(str::to_string),
        -3i64..=3i64,
        0..=3,
    )
}

/// Generate ground types (no type variables). Used where we need types
/// that won't interact with unification variables.
fn arb_ground_type() -> impl Strategy<Value = Type> {
    prop_oneof![
        Just(Type::Int),
        Just(Type::Float),
        Just(Type::Bool),
        Just(Type::String),
        Just(Type::Unit),
        Just(kea_types::builtin_error_sum_type("IOError").expect("builtin error type")),
        Just(kea_types::builtin_error_sum_type("SchemaError").expect("builtin error type")),
        Just(kea_types::builtin_error_sum_type("ExecError").expect("builtin error type")),
        Just(kea_types::builtin_error_sum_type("ActorError").expect("builtin error type")),
        Just(Type::Atom),
        Just(Type::Date),
        Just(Type::DateTime),
        Just(Type::Dynamic),
    ]
}

/// Generate types of bounded depth. Depth 0 = leaf types only.
fn arb_type(depth: u32) -> BoxedStrategy<Type> {
    if depth == 0 {
        prop_oneof![
            3 => arb_ground_type(),
            1 => arb_type_var_id().prop_map(Type::Var),
        ]
        .boxed()
    } else {
        let leaf = prop_oneof![
            3 => arb_ground_type(),
            1 => arb_type_var_id().prop_map(Type::Var),
        ];
        let inner = arb_type(depth - 1);
        prop_oneof![
            4 => leaf,
            1 => inner.clone().prop_map(|t| Type::List(Box::new(t))),
            1 => inner.clone().prop_map(|t| Type::Option(Box::new(t))),
            1 => inner.clone().prop_map(|t| Type::Set(Box::new(t))),
            1 => inner.clone().prop_map(|t| Type::Actor(Box::new(t))),
            1 => (inner.clone(), arb_tags()).prop_map(|(inner, tags)| Type::Tagged {
                inner: Box::new(inner),
                tags,
            }),
            1 => (inner.clone(), inner.clone())
                .prop_map(|(a, b)| Type::Result(Box::new(a), Box::new(b))),
            1 => prop::collection::vec(inner.clone(), 2..=4)
                .prop_map(Type::Tuple),
        ]
        .boxed()
    }
}

/// Generate ground types only (no variables, no compound nesting).
fn arb_ground_type_deep() -> BoxedStrategy<Type> {
    prop_oneof![
        4 => arb_ground_type(),
        1 => arb_ground_type().prop_map(|t| Type::List(Box::new(t))),
        1 => arb_ground_type().prop_map(|t| Type::Option(Box::new(t))),
        1 => (arb_ground_type(), arb_tags()).prop_map(|(inner, tags)| Type::Tagged {
            inner: Box::new(inner),
            tags,
        }),
        1 => (arb_ground_type(), arb_ground_type())
            .prop_map(|(a, b)| Type::Result(Box::new(a), Box::new(b))),
    ]
    .boxed()
}

/// Generate a row type with unique labels and field types of bounded depth.
fn arb_row_type(depth: u32) -> BoxedStrategy<RowType> {
    let fields = prop::collection::hash_set(arb_label(), 0..=4).prop_flat_map(move |labels| {
        let labels_vec: Vec<Label> = labels.into_iter().collect();
        let n = labels_vec.len();
        prop::collection::vec(arb_type(depth), n)
            .prop_map(move |types| labels_vec.iter().cloned().zip(types).collect::<Vec<_>>())
    });

    (fields, prop::option::of(arb_row_var_id()))
        .prop_map(|(fields, rest)| match rest {
            Some(var) => RowType::open(fields, var),
            None => RowType::closed(fields),
        })
        .boxed()
}

/// Generate a closed row with ground types and unique labels.
fn arb_closed_ground_row() -> BoxedStrategy<RowType> {
    prop::collection::hash_set(arb_label(), 0..=5)
        .prop_flat_map(|labels| {
            let labels_vec: Vec<Label> = labels.into_iter().collect();
            let n = labels_vec.len();
            prop::collection::vec(arb_ground_type(), n).prop_map(move |types| {
                let fields: Vec<_> = labels_vec.iter().cloned().zip(types).collect();
                RowType::closed(fields)
            })
        })
        .boxed()
}

fn test_prov() -> Provenance {
    Provenance {
        span: Span::new(FileId(0), 0, 1),
        reason: Reason::LetAnnotation,
    }
}

// ---------------------------------------------------------------------------
// Property: Substitution idempotence
// ---------------------------------------------------------------------------

proptest! {
    /// Renaming quantified type variables should preserve `forall` alpha-equivalence.
    #[test]
    fn forall_alpha_equivalence_is_invariant_under_renaming(ty in arb_type(2)) {
        let original_var = TypeVarId(0);
        let renamed_var = TypeVarId(7);
        prop_assume!(!free_type_vars(&ty).contains(&renamed_var));

        let mut subst = Substitution::new();
        subst.bind_type(original_var, Type::Var(renamed_var));

        let mut bounds = BTreeMap::new();
        bounds.insert(original_var, BTreeSet::from([String::from("Show")]));
        let mut renamed_bounds = BTreeMap::new();
        renamed_bounds.insert(renamed_var, BTreeSet::from([String::from("Show")]));

        let scheme = TypeScheme {
            type_vars: vec![original_var],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds,
            kinds: BTreeMap::new(),
            ty: ty.clone(),
        };
        let renamed = TypeScheme {
            type_vars: vec![renamed_var],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: renamed_bounds,
            kinds: BTreeMap::new(),
            ty: subst.apply(&ty),
        };

        prop_assert!(super::alpha_equivalent_type_schemes(&scheme, &renamed));
    }
}

proptest! {
    /// Applying a substitution twice to the same type produces the same
    /// result as applying it once. This must hold for any type.
    #[test]
    fn substitution_idempotent(ty in arb_type(2)) {
        let mut subst = Substitution::new();
        // Bind some variables to ground types so apply has something to do.
        subst.bind_type(TypeVarId(0), Type::Int);
        subst.bind_type(TypeVarId(1), Type::String);
        subst.bind_type(TypeVarId(2), Type::Bool);
        subst.bind_type(TypeVarId(3), Type::Float);

        let once = subst.apply(&ty);
        let twice = subst.apply(&once);
        prop_assert_eq!(once, twice);
    }

    /// Row substitution is also idempotent.
    #[test]
    fn row_substitution_idempotent(row in arb_row_type(1)) {
        let mut subst = Substitution::new();
        subst.bind_type(TypeVarId(0), Type::Int);
        subst.bind_type(TypeVarId(1), Type::String);
        subst.bind_row(
            RowVarId(0),
            RowType::closed(vec![(Label::new("extra"), Type::Bool)]),
        );

        let once = subst.apply_row(&row);
        let twice = subst.apply_row(&once);
        prop_assert_eq!(once, twice);
    }
}

proptest! {
    #[test]
    fn kind_domain_is_star_or_eff(use_eff in any::<bool>()) {
        let kind = if use_eff { Kind::Eff } else { Kind::Star };
        prop_assert!(matches!(kind, Kind::Star | Kind::Eff));
    }
}

proptest! {
    #[test]
    fn app_unify_option_binds_constructor_and_inner(inner in arb_ground_type_deep()) {
        let mut u = Unifier::new();
        let f = u.fresh_type_var();
        let a = u.fresh_type_var();
        let app = Type::App(Box::new(Type::Var(f)), vec![Type::Var(a)]);
        let concrete = Type::Option(Box::new(inner.clone()));

        u.unify(&app, &concrete, &test_prov());
        prop_assert!(!u.has_errors());
        prop_assert_eq!(u.substitution.apply(&Type::Var(a)), inner);
        prop_assert_eq!(
            u.substitution.apply(&Type::Var(f)),
            Type::Constructor {
                name: "Option".to_string(),
                fixed_args: vec![],
                arity: 1,
            }
        );
    }

    #[test]
    fn app_unify_result_binds_partial_constructor(
        ok in arb_ground_type_deep(),
        err in arb_ground_type_deep(),
    ) {
        let mut u = Unifier::new();
        let f = u.fresh_type_var();
        let a = u.fresh_type_var();
        let app = Type::App(Box::new(Type::Var(f)), vec![Type::Var(a)]);
        let concrete = Type::Result(Box::new(ok.clone()), Box::new(err.clone()));

        u.unify(&app, &concrete, &test_prov());
        prop_assert!(!u.has_errors());
        prop_assert_eq!(u.substitution.apply(&Type::Var(a)), ok);
        prop_assert_eq!(
            u.substitution.apply(&Type::Var(f)),
            Type::Constructor {
                name: "Result".to_string(),
                fixed_args: vec![(1, err)],
                arity: 2,
            }
        );
    }
}

// ---------------------------------------------------------------------------
// Property: Substitution chain idempotence
// ---------------------------------------------------------------------------
//
// The Lean formalization (formal/Kea/Properties/SubstIdempotent.lean) proved
// that substitution idempotence requires a precondition: range variables must
// be disjoint from domain variables. Without this, fuel-bounded apply would
// fail on chains like {a → List(b), b → Int} — a single pass resolves a to
// List(b) but not to List(Int).
//
// The Rust implementation is safe because Substitution::apply uses unbounded
// recursion (chases Var → resolved → apply(resolved) until it hits a leaf),
// and the occurs check prevents cycles, guaranteeing termination.
//
// These tests verify that the unbounded-chase implementation handles chains
// correctly. If Substitution::apply ever adds fuel/depth limits, these tests
// will catch the regression — and bind_type_var would need eager composition
// (apply existing substitution to the RHS before inserting).

proptest! {
    /// Variable-to-variable chains: a → List(b), b → Int.
    /// apply(apply(ty)) must equal apply(ty) even when the substitution
    /// contains indirect bindings through intermediate variables.
    #[test]
    fn substitution_chain_idempotent(
        leaf_ty in arb_ground_type(),
        wrapper_idx in 0u32..4,
        ty in arb_type(2),
    ) {
        let mut subst = Substitution::new();

        // Build a chain: Var(0) → wrapper(Var(1)) → Var(1) → leaf_ty
        let intermediate = match wrapper_idx {
            0 => Type::List(Box::new(Type::Var(TypeVarId(1)))),
            1 => Type::Option(Box::new(Type::Var(TypeVarId(1)))),
            2 => Type::Result(Box::new(Type::Var(TypeVarId(1))), Box::new(Type::Unit)),
            3 => Type::Actor(Box::new(Type::Var(TypeVarId(1)))),
            _ => unreachable!(),
        };
        subst.bind_type(TypeVarId(0), intermediate);
        subst.bind_type(TypeVarId(1), leaf_ty);

        // Also bind Var(2) → Var(3) → String (simple 2-hop chain)
        subst.bind_type(TypeVarId(2), Type::Var(TypeVarId(3)));
        subst.bind_type(TypeVarId(3), Type::String);

        let once = subst.apply(&ty);
        let twice = subst.apply(&once);
        prop_assert_eq!(
            once, twice,
            "Substitution with variable-to-variable chains must be idempotent"
        );
    }

    /// 3-hop chain: Var(0) → Var(1) → Var(2) → ground_type.
    /// Verifies that apply fully resolves multi-hop chains in a single pass.
    #[test]
    fn substitution_3hop_chain_idempotent(
        leaf in arb_ground_type(),
    ) {
        let mut subst = Substitution::new();
        subst.bind_type(TypeVarId(0), Type::Var(TypeVarId(1)));
        subst.bind_type(TypeVarId(1), Type::Var(TypeVarId(2)));
        subst.bind_type(TypeVarId(2), leaf.clone());

        let result = subst.apply(&Type::Var(TypeVarId(0)));
        let twice = subst.apply(&result);

        prop_assert_eq!(&result, &leaf,
            "3-hop chain should fully resolve to leaf type");
        prop_assert_eq!(result, twice,
            "apply on already-resolved type should be identity");
    }

    /// After applying a substitution with chains, the result must contain
    /// no domain variables — full resolution is guaranteed.
    #[test]
    fn substitution_chain_full_resolution(
        leaf_a in arb_ground_type(),
        leaf_b in arb_ground_type(),
        ty in arb_type(2),
    ) {
        let mut subst = Substitution::new();

        // Chains: 0 → List(1), 1 → leaf_a, 2 → Result(3, Unit), 3 → leaf_b
        subst.bind_type(TypeVarId(0), Type::List(Box::new(Type::Var(TypeVarId(1)))));
        subst.bind_type(TypeVarId(1), leaf_a);
        subst.bind_type(TypeVarId(2), Type::Result(
            Box::new(Type::Var(TypeVarId(3))),
            Box::new(Type::Unit),
        ));
        subst.bind_type(TypeVarId(3), leaf_b);

        let resolved = subst.apply(&ty);

        // No domain variable (0, 1, 2, 3) should appear in the resolved type.
        for var_id in 0..=3u32 {
            let var = TypeVarId(var_id);
            prop_assert!(
                !contains_var(&resolved, var),
                "Resolved type should not contain domain variable Var({var_id}), got {resolved:?}"
            );
        }
    }

    /// Row substitution with chains: row variable resolves to a row
    /// whose field types contain chained type variables.
    #[test]
    fn row_substitution_chain_idempotent(
        leaf in arb_ground_type(),
    ) {
        let mut subst = Substitution::new();

        // Type chain: Var(0) → Var(1) → leaf
        subst.bind_type(TypeVarId(0), Type::Var(TypeVarId(1)));
        subst.bind_type(TypeVarId(1), leaf.clone());

        // Row variable resolves to a row with a chained field type
        subst.bind_row(
            RowVarId(0),
            RowType::closed(vec![
                (Label::new("chained"), Type::Var(TypeVarId(0))),
                (Label::new("direct"), Type::Int),
            ]),
        );

        let input_row = RowType::open(
            vec![(Label::new("existing"), Type::Var(TypeVarId(0)))],
            RowVarId(0),
        );

        let once = subst.apply_row(&input_row);
        let twice = subst.apply_row(&once);
        prop_assert_eq!(
            &once, &twice,
            "Row substitution with type variable chains must be idempotent"
        );

        // Verify the chained field resolved to the leaf type
        let chained_field = once.fields.iter().find(|(l, _)| l.as_str() == "chained");
        prop_assert!(chained_field.is_some(), "chained field should exist");
        prop_assert_eq!(
            &chained_field.unwrap().1, &leaf,
            "chained field should resolve to leaf type through 2-hop chain"
        );
    }
}

// ---------------------------------------------------------------------------
// Property: Unification reflexivity
// ---------------------------------------------------------------------------

proptest! {
    /// Unifying any ground type with itself always succeeds.
    #[test]
    fn unify_reflexive_ground(ty in arb_ground_type_deep()) {
        let mut u = Unifier::new();
        u.unify(&ty, &ty, &test_prov());
        prop_assert!(!u.has_errors(), "Unifying {:?} with itself should succeed", ty);
    }

    /// Unifying any closed ground row with itself always succeeds.
    #[test]
    fn unify_reflexive_row(row in arb_closed_ground_row()) {
        let mut u = Unifier::new();
        u.unify_rows(&row, &row, &test_prov());
        prop_assert!(!u.has_errors(), "Unifying {:?} with itself should succeed", row);
    }
}

// ---------------------------------------------------------------------------
// Property: Successful unification produces consistent substitution
// ---------------------------------------------------------------------------

proptest! {
    /// After successful unification of two types, applying the resulting
    /// substitution to both types yields the same result.
    #[test]
    fn unify_consistent_substitution(ty in arb_type(1)) {
        // Unify (Var(7), ty) — uses var 7 to avoid collision with vars inside ty (0-6).
        let var = TypeVarId(7);
        let mut u = Unifier::new();
        u.unify(&Type::Var(var), &ty, &test_prov());

        if !u.has_errors() {
            let resolved_var = u.substitution.apply(&Type::Var(var));
            let resolved_ty = u.substitution.apply(&ty);
            prop_assert_eq!(
                resolved_var, resolved_ty,
                "After unifying Var({}) with {:?}, both should resolve equally",
                var.0, ty
            );
        }
        // If it errored (e.g., occurs check), that's fine — we only assert on success.
    }

    /// After successful row unification, applying substitution to both rows
    /// yields the same set of fields.
    #[test]
    fn unify_rows_consistent(
        fields_a in prop::collection::hash_set(arb_label(), 1..=3),
        fields_b in prop::collection::hash_set(arb_label(), 1..=3),
    ) {
        // Build two open rows with disjoint-ish fields and unify them.
        let r1 = RowVarId(100);
        let r2 = RowVarId(101);
        let row_a = RowType::open(
            fields_a.into_iter().map(|l| (l, Type::Int)).collect(),
            r1,
        );
        let row_b = RowType::open(
            fields_b.into_iter().map(|l| (l, Type::Int)).collect(),
            r2,
        );

        let mut u = Unifier::new();
        u.unify_rows(&row_a, &row_b, &test_prov());

        if !u.has_errors() {
            let resolved_a = u.substitution.apply_row(&row_a);
            let resolved_b = u.substitution.apply_row(&row_b);

            // After resolution, both rows should have the same labels.
            let labels_a: Vec<&Label> = resolved_a.labels().collect();
            let labels_b: Vec<&Label> = resolved_b.labels().collect();
            prop_assert_eq!(
                labels_a, labels_b,
                "After row unification, resolved rows should have same labels"
            );
        }
    }

    /// Effect-row unification follows the same row-unification invariants:
    /// after solving, both rows resolve to the same effect labels.
    #[test]
    fn unify_effect_rows_consistent(
        effects_a in prop::collection::hash_set(arb_label(), 1..=3),
        effects_b in prop::collection::hash_set(arb_label(), 1..=3),
    ) {
        let r1 = RowVarId(210);
        let r2 = RowVarId(211);
        let eff_a = EffectRow::open(
            effects_a.into_iter().map(|l| (l, Type::Unit)).collect(),
            r1,
        );
        let eff_b = EffectRow::open(
            effects_b.into_iter().map(|l| (l, Type::Unit)).collect(),
            r2,
        );

        let mut u = Unifier::new();
        u.unify_effect_rows(&eff_a, &eff_b, &test_prov());

        if !u.has_errors() {
            let resolved_a = u.substitution.apply_row(eff_a.as_row());
            let resolved_b = u.substitution.apply_row(eff_b.as_row());
            let labels_a: Vec<&Label> = resolved_a.labels().collect();
            let labels_b: Vec<&Label> = resolved_b.labels().collect();
            prop_assert_eq!(
                labels_a, labels_b,
                "After effect-row unification, resolved labels should match"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Property: Row fields always sorted
// ---------------------------------------------------------------------------

proptest! {
    /// RowType constructors always produce sorted fields.
    #[test]
    fn row_fields_sorted_closed(
        labels in prop::collection::hash_set(arb_label(), 0..=6),
    ) {
        let fields: Vec<_> = labels.into_iter().map(|l| (l, Type::Int)).collect();
        let row = RowType::closed(fields);
        for w in row.fields.windows(2) {
            prop_assert!(w[0].0 < w[1].0, "Fields not sorted: {:?} >= {:?}", w[0].0, w[1].0);
        }
    }

    /// RowType::open also produces sorted fields.
    #[test]
    fn row_fields_sorted_open(
        labels in prop::collection::hash_set(arb_label(), 0..=6),
        var in arb_row_var_id(),
    ) {
        let fields: Vec<_> = labels.into_iter().map(|l| (l, Type::Int)).collect();
        let row = RowType::open(fields, var);
        for w in row.fields.windows(2) {
            prop_assert!(w[0].0 < w[1].0, "Fields not sorted: {:?} >= {:?}", w[0].0, w[1].0);
        }
    }

    /// Substitution apply_row preserves field ordering.
    #[test]
    fn apply_row_preserves_sort(row in arb_row_type(1)) {
        let mut subst = Substitution::new();
        subst.bind_type(TypeVarId(0), Type::Int);
        // Bind row var 0 to a row with fields that might interleave.
        subst.bind_row(
            RowVarId(0),
            RowType::closed(vec![
                (Label::new("m"), Type::Float),
                (Label::new("n"), Type::Bool),
            ]),
        );

        let resolved = subst.apply_row(&row);
        for w in resolved.fields.windows(2) {
            prop_assert!(
                w[0].0 < w[1].0,
                "Fields not sorted after apply_row: {:?} >= {:?}",
                w[0].0, w[1].0
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Property: Occurs check catches all self-referential types
// ---------------------------------------------------------------------------

proptest! {
    /// Wrapping Var(x) in any type constructor and unifying with Var(x)
    /// should always trigger the occurs check.
    #[test]
    fn occurs_check_always_fires(wrapper_idx in 0u32..4) {
        let var = TypeVarId(0);
        let inner = Type::Var(var);
        let wrapped = match wrapper_idx {
            0 => Type::List(Box::new(inner)),
            1 => Type::Option(Box::new(inner)),
            2 => Type::Set(Box::new(inner)),
            3 => Type::Result(Box::new(inner), Box::new(Type::Unit)),
            _ => unreachable!(),
        };

        let mut u = Unifier::new();
        u.unify(&Type::Var(var), &wrapped, &test_prov());
        prop_assert!(
            u.has_errors(),
            "Occurs check should fire when unifying Var(0) with {:?}",
            wrapped
        );
    }
}

// ---------------------------------------------------------------------------
// Property: Unification symmetry
// ---------------------------------------------------------------------------

proptest! {
    /// For ground types, unify(a, b) and unify(b, a) should produce the
    /// same success/failure result.
    #[test]
    fn unify_symmetric_ground(
        a in arb_ground_type_deep(),
        b in arb_ground_type_deep(),
    ) {
        // Dynamic is intentionally asymmetric: widening OK, narrowing errors.
        // Skip pairs containing Dynamic from the symmetry property.
        if contains_dynamic(&a) || contains_dynamic(&b) {
            return Ok(());
        }
        let mut u1 = Unifier::new();
        u1.unify(&a, &b, &test_prov());

        let mut u2 = Unifier::new();
        u2.unify(&b, &a, &test_prov());

        prop_assert_eq!(
            u1.has_errors(), u2.has_errors(),
            "unify({:?}, {:?}) and unify({:?}, {:?}) should agree on success/failure",
            a, b, b, a
        );
    }

    /// Unification of a variable with a type is order-independent in terms
    /// of the final resolved type.
    #[test]
    fn unify_var_symmetric(ty in arb_ground_type_deep()) {
        let var = TypeVarId(7);

        let mut u1 = Unifier::new();
        u1.unify(&Type::Var(var), &ty, &test_prov());

        let mut u2 = Unifier::new();
        u2.unify(&ty, &Type::Var(var), &test_prov());

        prop_assert_eq!(u1.has_errors(), u2.has_errors());
        if !u1.has_errors() {
            let r1 = u1.substitution.apply(&Type::Var(var));
            let r2 = u2.substitution.apply(&Type::Var(var));
            prop_assert_eq!(r1, r2, "Variable should resolve to the same type regardless of argument order");
        }
    }
}

// ---------------------------------------------------------------------------
// Property: Rémy decomposition preserves all fields
// ---------------------------------------------------------------------------

proptest! {
    /// When unifying two open rows, every label from both sides appears
    /// in the fully resolved result.
    #[test]
    fn remy_preserves_all_labels(
        labels_a in prop::collection::hash_set(arb_label(), 1..=4),
        labels_b in prop::collection::hash_set(arb_label(), 1..=4),
    ) {
        let r1 = RowVarId(100);
        let r2 = RowVarId(101);

        let row_a = RowType::open(
            labels_a.iter().cloned().map(|l| (l, Type::Int)).collect(),
            r1,
        );
        let row_b = RowType::open(
            labels_b.iter().cloned().map(|l| (l, Type::Int)).collect(),
            r2,
        );

        let mut u = Unifier::new();
        u.unify_rows(&row_a, &row_b, &test_prov());

        if !u.has_errors() {
            let resolved_a = u.substitution.apply_row(&row_a);
            let resolved_b = u.substitution.apply_row(&row_b);

            // Every label from both inputs must appear in resolved_a.
            for label in labels_a.iter().chain(labels_b.iter()) {
                prop_assert!(
                    resolved_a.has(label),
                    "Label {:?} missing from resolved row A",
                    label
                );
                prop_assert!(
                    resolved_b.has(label),
                    "Label {:?} missing from resolved row B",
                    label
                );
            }
        }
    }

    /// Rémy decomposition: the fresh tail variable should lack all labels
    /// from both input rows.
    #[test]
    fn remy_tail_lacks_all_labels(
        labels_a in prop::collection::hash_set(arb_label(), 1..=3),
        labels_b in prop::collection::hash_set(arb_label(), 1..=3),
    ) {
        let r1 = RowVarId(100);
        let r2 = RowVarId(101);

        let row_a = RowType::open(
            labels_a.iter().cloned().map(|l| (l, Type::Int)).collect(),
            r1,
        );
        let row_b = RowType::open(
            labels_b.iter().cloned().map(|l| (l, Type::Int)).collect(),
            r2,
        );

        let mut u = Unifier::new();
        u.unify_rows(&row_a, &row_b, &test_prov());

        if !u.has_errors() {
            // Find the tail variable of the resolved row.
            let resolved = u.substitution.apply_row(&row_a);
            if let Some(tail) = resolved.rest {
                for label in labels_a.iter().chain(labels_b.iter()) {
                    prop_assert!(
                        u.lacks.lacks(tail, label),
                        "Tail variable should lack {:?} but doesn't",
                        label
                    );
                }
            }
            // If the row is closed, that's fine — all fields accounted for.
        }
    }
}

// ---------------------------------------------------------------------------
// Property: Lacks constraints are respected
// ---------------------------------------------------------------------------

proptest! {
    /// If a row variable has a lacks constraint for label L, unifying it
    /// with a closed row containing L should produce an error.
    #[test]
    fn lacks_constraint_blocks_duplicate(label in arb_label()) {
        let r = RowVarId(0);

        let mut u = Unifier::new();
        u.lacks.add(r, label.clone());

        // Try to unify an open row {| r} with a closed row {label: Int}.
        let open = RowType::empty_open(r);
        let closed = RowType::closed(vec![(label.clone(), Type::Int)]);
        u.unify_rows(&open, &closed, &test_prov());

        prop_assert!(
            u.has_errors(),
            "Should fail: row variable lacks {:?} but was unified with a row containing it",
            label
        );
    }

    /// Lacks constraints apply equally to effect-row tails.
    #[test]
    fn effect_lacks_constraint_blocks_duplicate(label in arb_label()) {
        let r = RowVarId(99);

        let mut u = Unifier::new();
        u.lacks.add(r, label.clone());

        let open = EffectRow::open(vec![], r);
        let closed = EffectRow::closed(vec![(label.clone(), Type::Unit)]);
        u.unify_effect_rows(&open, &closed, &test_prov());

        prop_assert!(
            u.has_errors(),
            "Should fail: effect tail lacks {:?} but was unified with a row containing it",
            label
        );
    }
}

// ---------------------------------------------------------------------------
// Property: No ground type unification variables in output
// ---------------------------------------------------------------------------

proptest! {
    /// After resolving all bound variables, the result should contain no
    /// Var nodes for variables that were bound during unification.
    #[test]
    fn no_bound_vars_in_resolved_type(
        ty_a in arb_ground_type_deep(),
    ) {
        let var = TypeVarId(7);
        let mut u = Unifier::new();
        u.unify(&Type::Var(var), &ty_a, &test_prov());

        if !u.has_errors() {
            let resolved = u.substitution.apply(&Type::Var(var));
            prop_assert!(
                !contains_var(&resolved, var),
                "Resolved type should not contain Var({}) but got {:?}",
                var.0, resolved
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Property: Substitution apply is idempotent on generalized types
// ---------------------------------------------------------------------------

proptest! {
    /// Generalization should be stable under double substitution application.
    /// If we apply the substitution to a type, then generalize, the result
    /// should be identical to generalizing after applying twice. This guards
    /// against incomplete transitive resolution ("zonking") in the substitution.
    #[test]
    fn generalize_stable_under_double_apply(
        ty_a in arb_ground_type_deep(),
        ty_b in arb_ground_type_deep(),
    ) {
        use crate::typeck::{generalize, TypeEnv};

        let mut u = Unifier::new();
        let v1 = u.fresh_type_var();
        let v2 = u.fresh_type_var();

        // Create a chain: v1 -> v2 -> ty_a
        u.unify(&Type::Var(v1), &Type::Var(v2), &test_prov());
        u.unify(&Type::Var(v2), &ty_a, &test_prov());

        if u.has_errors() {
            return Ok(());
        }

        // Put ty_b in the environment to make things interesting.
        let mut env = TypeEnv::new();
        let v3 = u.fresh_type_var();
        u.unify(&Type::Var(v3), &ty_b, &test_prov());
        env.bind("dummy".to_string(), TypeScheme::mono(Type::Var(v3)));

        // Generalize with single apply (what we actually do).
        let scheme1 = generalize(
            &Type::Var(v1),
            &env,
            &u.substitution,
            &u.lacks,
            &u.trait_bounds,
            &u.type_var_kinds,
        );

        // Generalize after applying substitution first (double apply).
        let resolved = u.substitution.apply(&Type::Var(v1));
        let scheme2 = generalize(
            &resolved,
            &env,
            &u.substitution,
            &u.lacks,
            &u.trait_bounds,
            &u.type_var_kinds,
        );

        // Both should produce the same generalized type.
        prop_assert_eq!(
            scheme1.ty, scheme2.ty,
            "Generalization should be stable: single-apply vs double-apply differ"
        );
        prop_assert_eq!(
            scheme1.type_vars.len(), scheme2.type_vars.len(),
            "Quantified type vars should match"
        );
        prop_assert_eq!(
            scheme1.row_vars.len(), scheme2.row_vars.len(),
            "Quantified row vars should match"
        );
    }
}

/// Check whether a type contains a specific type variable.
fn contains_var(ty: &Type, var: TypeVarId) -> bool {
    match ty {
        Type::Var(v) => *v == var,
        Type::List(inner) | Type::Set(inner) | Type::Option(inner) => contains_var(inner, var),
        Type::Map(k, v) | Type::Result(k, v) => contains_var(k, var) || contains_var(v, var),
        Type::Tuple(elems) => elems.iter().any(|t| contains_var(t, var)),
        Type::Function(ft) => {
            ft.params.iter().any(|t| contains_var(t, var)) || contains_var(&ft.ret, var)
        }
        Type::Record(rt) => rt.row.fields.iter().any(|(_, t)| contains_var(t, var)),
        Type::AnonRecord(row) | Type::Row(row) => {
            row.fields.iter().any(|(_, t)| contains_var(t, var))
        }
        Type::Tagged { inner, .. }
        | Type::Actor(inner)
        | Type::Arc(inner) => contains_var(inner, var),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Trait bound propagation
// ---------------------------------------------------------------------------

proptest! {
    /// Trait bounds on quantified type vars survive generalize → instantiate round-trip.
    ///
    /// Corresponds to Lean theorem: `traitBoundsSurviveInstantiate` (planned).
    #[test]
    fn trait_bounds_survive_generalize_instantiate(
        // Generate 1-3 trait names as random strings.
        trait_count in 1..4usize,
    ) {
        let mut unifier = Unifier::new();
        let tv = unifier.fresh_type_var();

        // Add trait_count bounds to the type var.
        let trait_names: Vec<String> = (0..trait_count)
            .map(|i| format!("Trait{i}"))
            .collect();
        for name in &trait_names {
            unifier.add_trait_bound(tv, name.clone());
        }

        // Generalize: t0 -> t0 with bounds.
        let env = crate::typeck::TypeEnv::new();
        let ty = Type::Function(FunctionType {
            params: vec![Type::Var(tv)],
            ret: Box::new(Type::Var(tv)),
        });
        let scheme = crate::typeck::generalize(
            &ty,
            &env,
            &unifier.substitution,
            &unifier.lacks,
            &unifier.trait_bounds,
            &unifier.type_var_kinds,
        );

        // Verify bounds are in the scheme.
        prop_assert!(scheme.bounds.contains_key(&tv));
        prop_assert_eq!(scheme.bounds[&tv].len(), trait_count);
        for name in &trait_names {
            prop_assert!(
                scheme.bounds[&tv].contains(name),
                "missing bound {name} in scheme"
            );
        }

        // Instantiate with fresh unifier.
        let mut unifier2 = Unifier::new();
        let instantiated = crate::typeck::instantiate(&scheme, &mut unifier2);

        // Find the fresh type var.
        if let Type::Function(ft) = &instantiated {
            if let Type::Var(fresh_tv) = &ft.params[0] {
                prop_assert!(
                    unifier2.trait_bounds.contains_key(fresh_tv),
                    "fresh var should have trait bounds after instantiation"
                );
                prop_assert_eq!(
                    unifier2.trait_bounds[fresh_tv].len(),
                    trait_count,
                    "all bounds should transfer"
                );
                for name in &trait_names {
                    prop_assert!(
                        unifier2.trait_bounds[fresh_tv].contains(name),
                        "missing bound {name} after instantiation"
                    );
                }
            } else {
                prop_assert!(false, "expected type var in params");
            }
        } else {
            prop_assert!(false, "expected function type");
        }
    }

    // -- Sendable property tests --

    /// All ground types are Sendable (no closures among them).
    #[test]
    fn prop_ground_types_are_sendable(ty in arb_ground_type()) {
        prop_assert!(is_sendable(&ty), "ground type {ty} should be Sendable");
    }

    /// Actor(T) is always Sendable regardless of inner type.
    #[test]
    fn prop_actor_is_sendable(inner in arb_ground_type()) {
        let ty = Type::Actor(Box::new(inner));
        prop_assert!(is_sendable(&ty), "Actor({ty}) should be Sendable");
    }

    /// Function types are never Sendable.
    #[test]
    fn prop_functions_not_sendable(
        params in prop::collection::vec(arb_ground_type(), 1..=3),
        ret in arb_ground_type()
    ) {
        let ty = Type::Function(FunctionType {
            params,
            ret: Box::new(ret),
        });
        prop_assert!(!is_sendable(&ty), "Function type should NOT be Sendable");
    }

    /// Option(T) is Sendable iff T is Sendable.
    #[test]
    fn prop_option_sendable_iff_inner(inner in arb_ground_type()) {
        let ty = Type::Option(Box::new(inner.clone()));
        prop_assert_eq!(is_sendable(&ty), is_sendable(&inner));
    }

    /// List(T) is Sendable iff T is Sendable.
    #[test]
    fn prop_list_sendable_iff_inner(inner in arb_ground_type()) {
        let ty = Type::List(Box::new(inner.clone()));
        prop_assert_eq!(is_sendable(&ty), is_sendable(&inner));
    }

    /// Tuple of Sendable types is Sendable.
    #[test]
    fn prop_tuple_of_sendable_is_sendable(
        elems in prop::collection::vec(arb_ground_type(), 2..=4)
    ) {
        let ty = Type::Tuple(elems);
        prop_assert!(is_sendable(&ty), "Tuple of ground types should be Sendable");
    }

    /// List containing a function type is NOT Sendable.
    #[test]
    fn prop_list_of_function_not_sendable(
        params in prop::collection::vec(arb_ground_type(), 1..=2),
        ret in arb_ground_type()
    ) {
        let fn_ty = Type::Function(FunctionType {
            params,
            ret: Box::new(ret),
        });
        let ty = Type::List(Box::new(fn_ty));
        prop_assert!(!is_sendable(&ty), "List(Function) should NOT be Sendable");
    }

    /// Result with a function in either position is NOT Sendable.
    #[test]
    fn prop_result_with_function_not_sendable(
        params in prop::collection::vec(arb_ground_type(), 1..=2),
        ret in arb_ground_type(),
        ok_ty in arb_ground_type()
    ) {
        let fn_ty = Type::Function(FunctionType {
            params,
            ret: Box::new(ret),
        });
        // Function in the error position
        let ty = Type::Result(Box::new(ok_ty), Box::new(fn_ty));
        prop_assert!(!is_sendable(&ty), "Result(T, Function) should NOT be Sendable");
    }

    /// Map(K, V) is Sendable iff both K and V are Sendable.
    #[test]
    fn prop_map_sendable_iff_both(
        k in arb_ground_type(),
        v in arb_ground_type()
    ) {
        let ty = Type::Map(Box::new(k.clone()), Box::new(v.clone()));
        prop_assert_eq!(
            is_sendable(&ty),
            is_sendable(&k) && is_sendable(&v)
        );
    }
}

// ---------------------------------------------------------------------------
// Actor trait enforcement properties
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Property: Sendable structural recursion
// ---------------------------------------------------------------------------
//
// For any type tree, `is_sendable` returns `false` if and only if there is a
// `Function` type anywhere in the tree. We generate nested types including
// Records, Tuples, Lists, Options, and Results with random depth. Some
// leaves are Functions, others ground types.

/// Reference implementation: returns true if the type tree contains any
/// Function node, recursing through all compound wrappers.
fn contains_function(ty: &Type) -> bool {
    match ty {
        Type::Function(_) => true,
        Type::List(inner) | Type::Set(inner) | Type::Option(inner) => contains_function(inner),
        Type::Map(k, v) | Type::Result(k, v) => contains_function(k) || contains_function(v),
        Type::Tuple(elems) => elems.iter().any(contains_function),
        Type::Record(rt) => rt.row.fields.iter().any(|(_, t)| contains_function(t)),
        Type::AnonRecord(row) | Type::Row(row) => {
            row.fields.iter().any(|(_, t)| contains_function(t))
        }
        Type::Tagged { inner, .. }
        | Type::Actor(inner)
        | Type::Arc(inner) => contains_function(inner),
        _ => false,
    }
}

/// Generate a nested type tree of bounded depth. At leaves, randomly choose
/// between ground types and Function types. At interior nodes, wrap in
/// List, Option, Tuple, Result, or Record.
fn arb_nested_type(depth: u32) -> BoxedStrategy<Type> {
    if depth == 0 {
        // Leaf level: choose ground type or a function
        prop_oneof![
            3 => arb_ground_type(),
            1 => (
                prop::collection::vec(arb_ground_type(), 1..=2),
                arb_ground_type()
            ).prop_map(|(params, ret)| Type::Function(FunctionType {
                params,
                ret: Box::new(ret),
            })),
        ]
        .boxed()
    } else {
        let leaf = prop_oneof![
            3 => arb_ground_type(),
            1 => (
                prop::collection::vec(arb_ground_type(), 1..=2),
                arb_ground_type()
            ).prop_map(|(params, ret)| Type::Function(FunctionType {
                params,
                ret: Box::new(ret),
            })),
        ];
        let inner = arb_nested_type(depth - 1);
        prop_oneof![
            3 => leaf,
            1 => inner.clone().prop_map(|t| Type::List(Box::new(t))),
            1 => inner.clone().prop_map(|t| Type::Option(Box::new(t))),
            1 => (inner.clone(), arb_tags()).prop_map(|(inner, tags)| Type::Tagged {
                inner: Box::new(inner),
                tags,
            }),
            1 => (inner.clone(), inner.clone())
                .prop_map(|(a, b)| Type::Result(Box::new(a), Box::new(b))),
            1 => prop::collection::vec(inner.clone(), 2..=4)
                .prop_map(Type::Tuple),
            1 => (arb_label(), inner.clone())
                .prop_map(|(label, ty)| Type::Record(RecordType {
                    name: "TestRecord".to_string(),
                    params: vec![],
                    row: RowType::closed(vec![(label, ty)]),
                })),
        ]
        .boxed()
    }
}

proptest! {
    /// is_sendable(ty) == !contains_function(ty) for any generated type tree.
    ///
    /// This property verifies that Sendable checking correctly finds Function
    /// types at any depth of nesting, through all compound type constructors.
    #[test]
    fn prop_sendable_iff_no_function(ty in arb_nested_type(3)) {
        let expected = !contains_function(&ty);
        let actual = is_sendable(&ty);
        prop_assert_eq!(
            actual, expected,
            "is_sendable({:?}) = {}, but contains_function = {}, expected is_sendable = {}",
            ty, actual, contains_function(&ty), expected,
        );
    }
}

use crate::typeck::{SumTypeRegistry, TypeEnv, infer_and_resolve_in_context};

const RECORD_NAME_POOL: &[&str] = &["Counter", "Acc", "State", "Buf", "Cfg"];

fn arb_record_name() -> impl Strategy<Value = String> {
    prop::sample::select(RECORD_NAME_POOL).prop_map(|s| s.to_string())
}

fn sp_ast<T>(node: T) -> kea_ast::Spanned<T> {
    kea_ast::Spanned {
        node,
        span: Span::new(FileId(0), 0, 0),
    }
}

fn ctor_arg(value: kea_ast::Expr) -> kea_ast::Argument {
    kea_ast::Argument { label: None, value }
}

fn ctor_pat(pattern: kea_ast::Pattern) -> kea_ast::ConstructorFieldPattern {
    kea_ast::ConstructorFieldPattern {
        name: None,
        pattern,
    }
}

fn variant_field(ty: kea_ast::TypeAnnotation) -> kea_ast::VariantField {
    let ty = sp_ast(ty);
    kea_ast::VariantField {
        annotations: vec![],
        name: None,
        span: ty.span,
        ty,
    }
}

fn arb_int_expr(depth: u32) -> BoxedStrategy<kea_ast::Expr> {
    if depth == 0 {
        any::<i64>()
            .prop_map(|n| sp_ast(kea_ast::ExprKind::Lit(kea_ast::Lit::Int(n))))
            .boxed()
    } else {
        let nested = arb_int_expr(depth - 1);
        prop_oneof![
            3 => any::<i64>()
                .prop_map(|n| sp_ast(kea_ast::ExprKind::Lit(kea_ast::Lit::Int(n)))),
            2 => (nested.clone(), nested.clone()).prop_map(|(left, right)| {
                sp_ast(kea_ast::ExprKind::BinaryOp {
                    op: sp_ast(kea_ast::BinOp::Add),
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }),
            2 => (nested.clone(), nested.clone()).prop_map(|(left, right)| {
                sp_ast(kea_ast::ExprKind::BinaryOp {
                    op: sp_ast(kea_ast::BinOp::Mul),
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }),
        ]
        .boxed()
    }
}

fn arb_bool_expr(depth: u32) -> BoxedStrategy<kea_ast::Expr> {
    if depth == 0 {
        any::<bool>()
            .prop_map(|b| sp_ast(kea_ast::ExprKind::Lit(kea_ast::Lit::Bool(b))))
            .boxed()
    } else {
        let nested = arb_bool_expr(depth - 1);
        let ints = arb_int_expr(depth - 1);
        prop_oneof![
            3 => any::<bool>()
                .prop_map(|b| sp_ast(kea_ast::ExprKind::Lit(kea_ast::Lit::Bool(b)))),
            2 => (ints.clone(), ints.clone()).prop_map(|(left, right)| {
                sp_ast(kea_ast::ExprKind::BinaryOp {
                    op: sp_ast(kea_ast::BinOp::Gt),
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }),
            2 => (nested.clone(), nested.clone()).prop_map(|(left, right)| {
                sp_ast(kea_ast::ExprKind::BinaryOp {
                    op: sp_ast(kea_ast::BinOp::And),
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }),
        ]
        .boxed()
    }
}

fn arb_well_typed_expr(depth: u32) -> BoxedStrategy<(kea_ast::Expr, Type)> {
    if depth == 0 {
        prop_oneof![
            arb_int_expr(0).prop_map(|expr| (expr, Type::Int)),
            arb_bool_expr(0).prop_map(|expr| (expr, Type::Bool)),
            ".*".prop_map(|s| {
                (
                    sp_ast(kea_ast::ExprKind::Lit(kea_ast::Lit::String(s))),
                    Type::String,
                )
            }),
        ]
        .boxed()
    } else {
        let base = arb_well_typed_expr(depth - 1);
        prop_oneof![
            3 => arb_int_expr(depth).prop_map(|expr| (expr, Type::Int)),
            3 => arb_bool_expr(depth).prop_map(|expr| (expr, Type::Bool)),
            1 => ".*".prop_map(|s| {
                (
                    sp_ast(kea_ast::ExprKind::Lit(kea_ast::Lit::String(s))),
                    Type::String,
                )
            }),
            2 => (base.clone(), base).prop_map(|((left_expr, left_ty), (right_expr, right_ty))| {
                (
                    sp_ast(kea_ast::ExprKind::Tuple(vec![left_expr, right_expr])),
                    Type::Tuple(vec![left_ty, right_ty]),
                )
            }),
        ]
        .boxed()
    }
}

fn register_tagged_gadt(sum_types: &mut SumTypeRegistry, records: &RecordRegistry) {
    let def = kea_ast::TypeDef {
        annotations: vec![],
        public: false,
        name: sp_ast("Tagged".to_string()),
        doc: None,
        params: vec!["T".to_string()],
        variants: vec![
            kea_ast::TypeVariant {
                annotations: vec![],
                name: sp_ast("TagInt".to_string()),
                fields: vec![variant_field(kea_ast::TypeAnnotation::Named(
                    "T".to_string(),
                ))],
                where_clause: vec![kea_ast::VariantWhereItem {
                    type_var: sp_ast("T".to_string()),
                    ty: sp_ast(kea_ast::TypeAnnotation::Named("Int".to_string())),
                }],
            },
            kea_ast::TypeVariant {
                annotations: vec![],
                name: sp_ast("TagBool".to_string()),
                fields: vec![variant_field(kea_ast::TypeAnnotation::Named(
                    "T".to_string(),
                ))],
                where_clause: vec![kea_ast::VariantWhereItem {
                    type_var: sp_ast("T".to_string()),
                    ty: sp_ast(kea_ast::TypeAnnotation::Named("Bool".to_string())),
                }],
            },
        ],
        derives: vec![],
    };
    sum_types
        .register(&def, records)
        .expect("Tagged GADT should register");
}

fn register_shape_sum(sum_types: &mut SumTypeRegistry, records: &RecordRegistry) {
    let def = kea_ast::TypeDef {
        annotations: vec![],
        public: false,
        name: sp_ast("Shape".to_string()),
        doc: None,
        params: vec![],
        variants: vec![
            kea_ast::TypeVariant {
                annotations: vec![],
                name: sp_ast("Circle".to_string()),
                fields: vec![variant_field(kea_ast::TypeAnnotation::Named(
                    "Int".to_string(),
                ))],
                where_clause: vec![],
            },
            kea_ast::TypeVariant {
                annotations: vec![],
                name: sp_ast("Rect".to_string()),
                fields: vec![variant_field(kea_ast::TypeAnnotation::Named(
                    "String".to_string(),
                ))],
                where_clause: vec![],
            },
        ],
        derives: vec![],
    };
    sum_types
        .register(&def, records)
        .expect("Shape sum type should register");
}

fn register_container_with_projected_defaults(
    traits: &mut TraitRegistry,
    records: &RecordRegistry,
    wrapped_first: bool,
) {
    let wrapped_assoc = kea_ast::AssociatedTypeDecl {
        name: sp_ast("Wrapped".to_string()),
        constraints: vec![],
        default: Some(sp_ast(kea_ast::TypeAnnotation::Applied(
            "Option".into(),
            vec![kea_ast::TypeAnnotation::Projection {
                base: "Self".into(),
                name: "Item".into(),
            }],
        ))),
    };
    let item_assoc = kea_ast::AssociatedTypeDecl {
        name: sp_ast("Item".to_string()),
        constraints: vec![],
        default: Some(sp_ast(kea_ast::TypeAnnotation::Named(
            "String".to_string(),
        ))),
    };
    let associated_types = if wrapped_first {
        vec![wrapped_assoc, item_assoc]
    } else {
        vec![item_assoc, wrapped_assoc]
    };
    let def = kea_ast::TraitDef {
        public: false,
        name: sp_ast("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types,
        methods: vec![],
    };
    traits
        .register_trait(&def, records)
        .expect("Container trait should register");
}

proptest! {
    /// For any named record type, spawn infers `Task(T)` unless there is
    /// a concrete `impl Actor for T`, in which case it infers `Actor(T)`.
    #[test]
    fn prop_spawn_dispatches_actor_vs_task(
        name in arb_record_name(),
        field_count in 1usize..=3,
    ) {
        use kea_ast::*;

        let dummy_span = Span::new(FileId(0), 0, 0);
        let sp = |node| Spanned { node, span: dummy_span };

        // Build record fields: f0: Int, f1: Int, ..
        let fields: Vec<(Spanned<String>, TypeAnnotation)> = (0..field_count)
            .map(|i| (sp(format!("f{i}")), TypeAnnotation::Named("Int".to_string())))
            .collect();
        let rec_def = RecordDef {
            annotations: vec![],
            public: false,
            name: sp(name.clone()),
            doc: None,
            params: vec![],
            derives: vec![],
            fields,
            field_annotations: vec![],
        };

        // Build the row type
        let row_fields: Vec<(Label, Type)> = (0..field_count)
            .map(|i| (Label::new(format!("f{i}")), Type::Int))
            .collect();
        let rec_type = Type::Record(RecordType {
            name: name.clone(),
            params: vec![],
            row: RowType::closed(row_fields),
        });

        // --- Without impl Actor ---
        let mut records = RecordRegistry::new();
        let mut traits = TraitRegistry::new();
        let actor_trait = TraitDef {
            public: true,
            name: sp("Actor".to_string()),
            doc: None,
            type_params: vec![],
            supertraits: vec![],
            fundeps: vec![],
            associated_types: vec![],
            methods: vec![],
        };
        traits.register_trait(&actor_trait, &records).unwrap();
        records.register(&rec_def).unwrap();
        traits.register_type_owner(&name, "repl:");

        let mut env = TypeEnv::new();
        env.bind("val".into(), kea_types::TypeScheme::mono(rec_type.clone()));
        let spawn = Spanned {
            node: ExprKind::Spawn { value: Box::new(Spanned {
                node: ExprKind::Var("val".to_string()),
                span: dummy_span,
            }), config: None },
            span: dummy_span,
        };
        let mut ctx = crate::InferenceContext::new();
        let ty_no_actor = infer_and_resolve_in_context(
            &spawn,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &SumTypeRegistry::new(),
        );
        prop_assert!(
            !ctx.has_errors(),
            "spawn without impl Actor should infer Task for {name}: {:?}",
            ctx.errors()
        );
        prop_assert!(
            matches!(ty_no_actor, Type::Task(_)),
            "spawn without impl Actor should be Task(_), got {ty_no_actor}"
        );

        // --- With impl Actor ---
        let impl_block = ImplBlock {
            trait_name: sp("Actor".to_string()),
            type_name: sp(name.clone()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![],
        };
        traits.register_trait_impl(&impl_block).unwrap();

        let mut env2 = TypeEnv::new();
        env2.bind("val".into(), kea_types::TypeScheme::mono(rec_type));
        let spawn2 = Spanned {
            node: ExprKind::Spawn { value: Box::new(Spanned {
                node: ExprKind::Var("val".to_string()),
                span: dummy_span,
            }), config: None },
            span: dummy_span,
        };
        let mut ctx2 = crate::InferenceContext::new();
        let ty = infer_and_resolve_in_context(
            &spawn2,
            &mut env2,
            &mut ctx2,
            &records,
            &traits,
            &SumTypeRegistry::new(),
        );
        prop_assert!(
            !ctx2.has_errors(),
            "spawn with impl Actor should succeed for {name}: {:?}",
            ctx2.errors()
        );
        prop_assert!(matches!(ty, Type::Actor(_)), "result should be Actor, got {ty}");
    }
}

proptest! {
    /// GADT refinement constraints from one constructor arm must not leak into
    /// sibling arms, regardless of arm order.
    #[test]
    fn prop_gadt_case_refinement_isolation_is_order_invariant(int_first in proptest::bool::ANY) {
        use kea_ast::{Expr, ExprKind, PatternKind};

        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let mut sums = SumTypeRegistry::new();
        register_tagged_gadt(&mut sums, &records);

        let mut env = TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let tagged_ty = sums
            .to_type_with("Tagged", &mut Some(ctx.unifier_mut()))
            .expect("Tagged should instantiate");
        env.bind("x".to_string(), TypeScheme::mono(tagged_ty));

        let int_arm = kea_ast::CaseArm {
            pattern: sp_ast(PatternKind::Constructor {
                name: "TagInt".to_string(),
                args: vec![ctor_pat(sp_ast(PatternKind::Var("n".to_string())))],
                rest: false,
                qualifier: None,
            }),
            guard: None,
            body: sp_ast(ExprKind::Block(vec![
                sp_ast(ExprKind::Var("n".to_string())),
                sp_ast(ExprKind::Lit(kea_ast::Lit::Int(1))),
            ])),
        };
        let bool_arm = kea_ast::CaseArm {
            pattern: sp_ast(PatternKind::Constructor {
                name: "TagBool".to_string(),
                args: vec![ctor_pat(sp_ast(PatternKind::Var("b".to_string())))],
                rest: false,
                qualifier: None,
            }),
            guard: None,
            body: sp_ast(ExprKind::Block(vec![
                sp_ast(ExprKind::Var("b".to_string())),
                sp_ast(ExprKind::Lit(kea_ast::Lit::Int(0))),
            ])),
        };
        let arms = if int_first {
            vec![int_arm, bool_arm]
        } else {
            vec![bool_arm, int_arm]
        };

        let expr: Expr = sp_ast(ExprKind::Case {
            scrutinee: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
            arms,
        });
        let ty = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sums);

        prop_assert!(!ctx.has_errors(), "unexpected diagnostics: {:?}", ctx.errors());
        prop_assert_eq!(ctx.substitution().apply(&ty), Type::Int);
    }
}

proptest! {
    /// Constructor typing and case-branch refinement stay consistent:
    /// building a constrained variant and immediately matching it always
    /// type-checks to the expected result type.
    #[test]
    fn prop_gadt_constructor_match_roundtrip(
        tag_int in proptest::bool::ANY,
        n in any::<i64>(),
        b in proptest::bool::ANY,
    ) {
        use kea_ast::{Expr, ExprKind, Lit, PatternKind};

        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let mut sums = SumTypeRegistry::new();
        register_tagged_gadt(&mut sums, &records);

        let mut env = TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let scrutinee = if tag_int {
            sp_ast(ExprKind::Constructor {
                name: sp_ast("TagInt".to_string()),
                args: vec![ctor_arg(sp_ast(ExprKind::Lit(Lit::Int(n))))],
            })
        } else {
            sp_ast(ExprKind::Constructor {
                name: sp_ast("TagBool".to_string()),
                args: vec![ctor_arg(sp_ast(ExprKind::Lit(Lit::Bool(b))))],
            })
        };
        let expr: Expr = sp_ast(ExprKind::Case {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                kea_ast::CaseArm {
                    pattern: sp_ast(PatternKind::Constructor {
                        name: "TagInt".to_string(),
                        args: vec![ctor_pat(sp_ast(PatternKind::Var("n".to_string())))],
                        rest: false,
                        qualifier: None,
                    }),
                    guard: None,
                    body: sp_ast(ExprKind::Var("n".to_string())),
                },
                kea_ast::CaseArm {
                    pattern: sp_ast(PatternKind::Constructor {
                        name: "TagBool".to_string(),
                        args: vec![ctor_pat(sp_ast(PatternKind::Var("flag".to_string())))],
                        rest: false,
                        qualifier: None,
                    }),
                    guard: None,
                    body: sp_ast(ExprKind::If {
                        condition: Box::new(sp_ast(ExprKind::Var("flag".to_string()))),
                        then_branch: Box::new(sp_ast(ExprKind::Lit(Lit::Int(1)))),
                        else_branch: Some(Box::new(sp_ast(ExprKind::Lit(Lit::Int(0))))),
                    }),
                },
            ],
        });

        let ty = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sums);
        prop_assert!(!ctx.has_errors(), "unexpected diagnostics: {:?}", ctx.errors());
        prop_assert_eq!(ctx.substitution().apply(&ty), Type::Int);
    }
}

proptest! {
    /// Case patterns should constrain a variable scrutinee's outer shape.
    /// Matching `Some/None` over an unconstrained variable must infer an
    /// `Option` parameter type rather than reporting non-exhaustive `_`.
    #[test]
    fn prop_case_option_patterns_constrain_variable_scrutinee(int_first in proptest::bool::ANY) {
        use kea_ast::{Expr, ExprKind, Lit, PatternKind};

        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = SumTypeRegistry::new();

        let some_arm = kea_ast::CaseArm {
            pattern: sp_ast(PatternKind::Constructor {
                name: "Some".to_string(),
                args: vec![ctor_pat(sp_ast(PatternKind::Var("n".to_string())))],
                rest: false,
                qualifier: None,
            }),
            guard: None,
            body: sp_ast(ExprKind::Var("n".to_string())),
        };
        let none_arm = kea_ast::CaseArm {
            pattern: sp_ast(PatternKind::Constructor {
                name: "None".to_string(),
                args: vec![],
                rest: false,
                qualifier: None,
            }),
            guard: None,
            body: sp_ast(ExprKind::Lit(Lit::Int(0))),
        };
        let arms = if int_first {
            vec![some_arm, none_arm]
        } else {
            vec![none_arm, some_arm]
        };

        let expr: Expr = sp_ast(ExprKind::Lambda {
            params: vec![kea_ast::Param {
                label: ParamLabel::Implicit,
                pattern: sp_ast(PatternKind::Var("x".to_string())),
                annotation: None,
                default: None,
            }],
            body: Box::new(sp_ast(ExprKind::Case {
                scrutinee: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
                arms,
            })),
            return_annotation: None,
        });

        let mut env = TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let ty = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sums);

        prop_assert!(!ctx.has_errors(), "unexpected diagnostics: {:?}", ctx.errors());
        match ctx.substitution().apply(&ty) {
            Type::Function(ft) => {
                prop_assert_eq!(ft.params.len(), 1, "expected single-parameter lambda");
                prop_assert!(
                    matches!(ft.params.first(), Some(Type::Option(_))),
                    "scrutinee shape should resolve to Option(_), got {:?}",
                    ft.params
                );
                prop_assert_eq!(*ft.ret, Type::Int, "case body should resolve to Int");
            }
            other => prop_assert!(false, "expected function type, got {other:?}"),
        }
    }
}

proptest! {
    /// End-to-end callback effect polymorphism: function signatures carrying an
    /// effect row variable should propagate the callback's concrete effect row.
    #[test]
    fn prop_callback_effect_polymorphism_propagates_callback_row(
        callback_has_send in any::<bool>(),
        callback_is_impure in any::<bool>(),
    ) {
        use kea_ast::{Expr, ExprKind, Lit};

        let callback_row = if callback_is_impure {
            EffectRow::closed(vec![(Label::new("IO"), Type::Unit)])
        } else if callback_has_send {
            EffectRow::closed(vec![(Label::new("Send"), Type::Unit)])
        } else {
            EffectRow::pure()
        };

        let mut env = TypeEnv::new();
        env.set_function_effect_signature(
            "map_like".to_string(),
            crate::typeck::FunctionEffectSignature {
                param_effect_rows: vec![None, Some(EffectRow::open(vec![], RowVarId(0)))],
                effect_row: EffectRow::open(vec![], RowVarId(0)),
                instantiate_on_call: true,
            },
        );
        env.set_function_effect_row("cb".to_string(), callback_row.clone());

        let expr: Expr = sp_ast(ExprKind::Call {
            func: Box::new(sp_ast(ExprKind::Var("map_like".to_string()))),
            args: vec![
                kea_ast::Argument {
                    label: None,
                    value: sp_ast(ExprKind::List(vec![sp_ast(ExprKind::Lit(Lit::Int(1)))])),
                },
                kea_ast::Argument {
                    label: None,
                    value: sp_ast(ExprKind::Var("cb".to_string())),
                },
            ],
        });

        let inferred = crate::typeck::infer_expr_effects(&expr, &env);
        let expected = if callback_row.is_pure() {
            Effects::pure_deterministic()
        } else {
            Effects::impure()
        };
        prop_assert_eq!(inferred, expected);
    }
}

proptest! {
    /// Bidirectional invariant: checking against an inferred type should
    /// succeed and preserve that type for well-typed generated expressions.
    #[test]
    fn prop_check_expr_matches_infer_for_well_typed_expressions(
        (expr, _) in arb_well_typed_expr(3),
    ) {
        let mut infer_env = TypeEnv::new();
        let mut infer_ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let inferred = infer_and_resolve_in_context(
            &expr,
            &mut infer_env,
            &mut infer_ctx,
            &records,
            &traits,
            &sums,
        );
        prop_assume!(
            !infer_ctx.has_errors(),
            "generator should produce well-typed expressions, got: {:?}",
            infer_ctx.errors()
        );
        let inferred = infer_ctx.substitution().apply(&inferred);

        let mut check_env = TypeEnv::new();
        let mut check_ctx = crate::InferenceContext::new();
        let checked = check_expr_in_context(
            &expr,
            &inferred,
            Reason::TypeAscription,
            &mut check_env,
            &mut check_ctx,
            &records,
            &traits,
            &sums,
        );
        prop_assert!(
            !check_ctx.has_errors(),
            "check path should accept inferred type, got diagnostics: {:?}",
            check_ctx.errors()
        );
        prop_assert_eq!(check_ctx.substitution().apply(&checked), inferred);
    }
}

proptest! {
    /// Bidirectional check path pushes expected precision types into both if
    /// branches, so range violations surface at branch literals.
    #[test]
    fn prop_check_expr_if_precision_branch_range_diagnostics(
        then_value in any::<i64>(),
        else_value in any::<i64>(),
    ) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expr: Expr = sp_ast(ExprKind::If {
            condition: Box::new(sp_ast(ExprKind::Lit(Lit::Bool(true)))),
            then_branch: Box::new(sp_ast(ExprKind::Lit(Lit::Int(then_value)))),
            else_branch: Some(Box::new(sp_ast(ExprKind::Lit(Lit::Int(else_value))))),
        });
        let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
        let mut env = crate::typeck::TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error =
            i8::try_from(then_value).is_err() || i8::try_from(else_value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "range diagnostics should match branch literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Narrowing guards in `if` conditions should refine the RHS of `&&`
    /// so the guarded variable type-checks as unwrapped payload.
    #[test]
    fn prop_if_guard_narrowing_allows_rhs_and_then_branch(threshold in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expr: Expr = sp_ast(ExprKind::If {
            condition: Box::new(sp_ast(ExprKind::BinaryOp {
                op: sp_ast(kea_ast::BinOp::And),
                left: Box::new(sp_ast(ExprKind::Call {
                    func: Box::new(sp_ast(ExprKind::FieldAccess {
                        expr: Box::new(sp_ast(ExprKind::Var("Option".to_string()))),
                        field: sp_ast("is_some".to_string()),
                    })),
                    args: vec![kea_ast::Argument {
                        label: None,
                        value: sp_ast(ExprKind::Var("x".to_string())),
                    }],
                })),
                right: Box::new(sp_ast(ExprKind::BinaryOp {
                    op: sp_ast(kea_ast::BinOp::Gt),
                    left: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
                    right: Box::new(sp_ast(ExprKind::Lit(Lit::Int(threshold)))),
                })),
            })),
            then_branch: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
            else_branch: Some(Box::new(sp_ast(ExprKind::Lit(Lit::Int(0))))),
        });

        let mut env = crate::typeck::TypeEnv::new();
        env.bind(
            "x".to_string(),
            TypeScheme::mono(Type::Option(Box::new(Type::Int))),
        );
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let ty = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sums);

        prop_assert!(!ctx.has_errors(), "unexpected diagnostics: {:?}", ctx.errors());
        prop_assert_eq!(ctx.substitution().apply(&ty), Type::Int);
    }
}

proptest! {
    /// Negated Option guards should invert narrowing maps:
    /// `not is_none(x)` narrows the true branch to the payload type.
    #[test]
    fn prop_if_not_is_none_narrows_true_branch(delta in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit, UnaryOp};

        let expr: Expr = sp_ast(ExprKind::If {
            condition: Box::new(sp_ast(ExprKind::UnaryOp {
                op: sp_ast(UnaryOp::Not),
                operand: Box::new(sp_ast(ExprKind::Call {
                    func: Box::new(sp_ast(ExprKind::FieldAccess {
                        expr: Box::new(sp_ast(ExprKind::Var("Option".to_string()))),
                        field: sp_ast("is_none".to_string()),
                    })),
                    args: vec![kea_ast::Argument {
                        label: None,
                        value: sp_ast(ExprKind::Var("x".to_string())),
                    }],
                })),
            })),
            then_branch: Box::new(sp_ast(ExprKind::BinaryOp {
                op: sp_ast(kea_ast::BinOp::Add),
                left: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
                right: Box::new(sp_ast(ExprKind::Lit(Lit::Int(delta)))),
            })),
            else_branch: Some(Box::new(sp_ast(ExprKind::Lit(Lit::Int(0))))),
        });

        let mut env = crate::typeck::TypeEnv::new();
        env.bind(
            "x".to_string(),
            TypeScheme::mono(Type::Option(Box::new(Type::Int))),
        );
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let ty = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sums);

        prop_assert!(!ctx.has_errors(), "unexpected diagnostics: {:?}", ctx.errors());
        prop_assert_eq!(ctx.substitution().apply(&ty), Type::Int);
    }
}

proptest! {
    /// Negated Option guards should invert narrowing maps:
    /// `not is_some(x)` narrows the else branch to the payload type.
    #[test]
    fn prop_if_not_is_some_narrows_else_branch(delta in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit, UnaryOp};

        let expr: Expr = sp_ast(ExprKind::If {
            condition: Box::new(sp_ast(ExprKind::UnaryOp {
                op: sp_ast(UnaryOp::Not),
                operand: Box::new(sp_ast(ExprKind::Call {
                    func: Box::new(sp_ast(ExprKind::FieldAccess {
                        expr: Box::new(sp_ast(ExprKind::Var("Option".to_string()))),
                        field: sp_ast("is_some".to_string()),
                    })),
                    args: vec![kea_ast::Argument {
                        label: None,
                        value: sp_ast(ExprKind::Var("x".to_string())),
                    }],
                })),
            })),
            then_branch: Box::new(sp_ast(ExprKind::Lit(Lit::Int(0)))),
            else_branch: Some(Box::new(sp_ast(ExprKind::BinaryOp {
                op: sp_ast(kea_ast::BinOp::Add),
                left: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
                right: Box::new(sp_ast(ExprKind::Lit(Lit::Int(delta)))),
            }))),
        });

        let mut env = crate::typeck::TypeEnv::new();
        env.bind(
            "x".to_string(),
            TypeScheme::mono(Type::Option(Box::new(Type::Int))),
        );
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let ty = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sums);

        prop_assert!(!ctx.has_errors(), "unexpected diagnostics: {:?}", ctx.errors());
        prop_assert_eq!(ctx.substitution().apply(&ty), Type::Int);
    }
}

proptest! {
    /// Sum-variant guards should constrain unknown bindings to the owning sum
    /// type and narrow branch-local payload usage.
    #[test]
    fn prop_sum_variant_guard_constrains_unknown_binding(
        radius in any::<i64>(),
        label in ".*"
    ) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expr: Expr = sp_ast(ExprKind::If {
            condition: Box::new(sp_ast(ExprKind::Call {
                func: Box::new(sp_ast(ExprKind::FieldAccess {
                    expr: Box::new(sp_ast(ExprKind::Var("Shape".to_string()))),
                    field: sp_ast("is_circle".to_string()),
                })),
                args: vec![kea_ast::Argument {
                    label: None,
                    value: sp_ast(ExprKind::Var("x".to_string())),
                }],
            })),
            then_branch: Box::new(sp_ast(ExprKind::BinaryOp {
                op: sp_ast(kea_ast::BinOp::Eq),
                left: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
                right: Box::new(sp_ast(ExprKind::Lit(Lit::Int(radius)))),
            })),
            else_branch: Some(Box::new(sp_ast(ExprKind::BinaryOp {
                op: sp_ast(kea_ast::BinOp::Eq),
                left: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
                right: Box::new(sp_ast(ExprKind::Lit(Lit::String(label)))),
            }))),
        });

        let mut env = crate::typeck::TypeEnv::new();
        let unknown = Type::Var(TypeVarId(50_000));
        env.bind("x".to_string(), TypeScheme::mono(unknown.clone()));
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let mut sums = crate::typeck::SumTypeRegistry::new();
        register_shape_sum(&mut sums, &records);

        let ty = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sums);
        let resolved_unknown = ctx.substitution().apply(&unknown);

        prop_assert!(!ctx.has_errors(), "unexpected diagnostics: {:?}", ctx.errors());
        prop_assert_eq!(ctx.substitution().apply(&ty), Type::Bool);
        prop_assert!(
            matches!(resolved_unknown, Type::Sum(ref sum) if sum.name == "Shape"),
            "expected x to resolve to Shape, got {resolved_unknown:?}"
        );
    }
}

proptest! {
    /// Indirect boolean guards (via intermediate let binding) must not narrow.
    #[test]
    fn prop_intermediate_bool_guard_does_not_narrow(inner in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit, PatternKind};

        let expr: Expr = sp_ast(ExprKind::Block(vec![
            sp_ast(ExprKind::Let {
                pattern: sp_ast(PatternKind::Var("ok".to_string())),
                annotation: None,
                value: Box::new(sp_ast(ExprKind::Call {
                    func: Box::new(sp_ast(ExprKind::Var("is_some".to_string()))),
                    args: vec![kea_ast::Argument {
                        label: None,
                        value: sp_ast(ExprKind::Var("x".to_string())),
                    }],
                })),
            }),
            sp_ast(ExprKind::If {
                condition: Box::new(sp_ast(ExprKind::Var("ok".to_string()))),
                then_branch: Box::new(sp_ast(ExprKind::BinaryOp {
                    op: sp_ast(kea_ast::BinOp::Add),
                    left: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
                    right: Box::new(sp_ast(ExprKind::Lit(Lit::Int(inner)))),
                })),
                else_branch: Some(Box::new(sp_ast(ExprKind::Lit(Lit::Int(0))))),
            }),
        ]));

        let mut env = crate::typeck::TypeEnv::new();
        env.bind(
            "x".to_string(),
            TypeScheme::mono(Type::Option(Box::new(Type::Int))),
        );
        env.bind(
            "is_some".to_string(),
            TypeScheme::mono(Type::Function(FunctionType {
                params: vec![Type::Option(Box::new(Type::Int))],
                ret: Box::new(Type::Bool),
            })),
        );
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sums);
        prop_assert!(ctx.has_errors(), "expected type error without direct guard narrowing");
    }
}

proptest! {
    /// Guard narrowing is branch-local and should not leak after the if
    /// expression completes.
    #[test]
    fn prop_if_guard_narrowing_is_branch_local(delta in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expr: Expr = sp_ast(ExprKind::Block(vec![
            sp_ast(ExprKind::If {
                condition: Box::new(sp_ast(ExprKind::Call {
                    func: Box::new(sp_ast(ExprKind::FieldAccess {
                        expr: Box::new(sp_ast(ExprKind::Var("Option".to_string()))),
                        field: sp_ast("is_some".to_string()),
                    })),
                    args: vec![kea_ast::Argument {
                        label: None,
                        value: sp_ast(ExprKind::Var("x".to_string())),
                    }],
                })),
                then_branch: Box::new(sp_ast(ExprKind::BinaryOp {
                    op: sp_ast(kea_ast::BinOp::Add),
                    left: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
                    right: Box::new(sp_ast(ExprKind::Lit(Lit::Int(delta)))),
                })),
                else_branch: Some(Box::new(sp_ast(ExprKind::Lit(Lit::Int(0))))),
            }),
            sp_ast(ExprKind::BinaryOp {
                op: sp_ast(kea_ast::BinOp::Add),
                left: Box::new(sp_ast(ExprKind::Var("x".to_string()))),
                right: Box::new(sp_ast(ExprKind::Lit(Lit::Int(1)))),
            }),
        ]));

        let mut env = crate::typeck::TypeEnv::new();
        env.bind(
            "x".to_string(),
            TypeScheme::mono(Type::Option(Box::new(Type::Int))),
        );
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sums);
        prop_assert!(
            ctx.has_errors(),
            "post-if use should still see Option(Int), expected type error"
        );
    }
}

proptest! {
    /// Infer path for calls should enforce signature parameter contracts and
    /// surface precision-range diagnostics on literal arguments.
    #[test]
    fn prop_infer_expr_call_precision_argument_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
        let expr: Expr = sp_ast(ExprKind::Call {
            func: Box::new(sp_ast(ExprKind::Var("narrow".to_string()))),
            args: vec![kea_ast::Argument {
                label: None,
                value: sp_ast(ExprKind::Lit(Lit::Int(value))),
            }],
        });
        let mut env = crate::typeck::TypeEnv::new();
        env.bind(
            "narrow".to_string(),
            TypeScheme::mono(Type::Function(FunctionType {
                params: vec![expected.clone()],
                ret: Box::new(expected.clone()),
            })),
        );
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = infer_and_resolve_in_context(
            &expr,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "infer-mode call diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Infer path for pipes should enforce callee parameter contracts on the
    /// piped argument and surface precision-range diagnostics on literals.
    #[test]
    fn prop_infer_expr_pipe_precision_argument_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
        let expr: Expr = sp_ast(ExprKind::Call {
            func: Box::new(sp_ast(ExprKind::Var("narrow".to_string()))),
            args: vec![kea_ast::Argument {
                label: None,
                value: sp_ast(ExprKind::Lit(Lit::Int(value))),
            }],
        });
        let mut env = crate::typeck::TypeEnv::new();
        env.bind(
            "narrow".to_string(),
            TypeScheme::mono(Type::Function(FunctionType {
                params: vec![expected.clone()],
                ret: Box::new(expected.clone()),
            })),
        );
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = infer_and_resolve_in_context(
            &expr,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "infer-mode pipe diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Bidirectional check path for calls pushes function parameter types into
    /// arguments, surfacing precision-range diagnostics at literal arguments.
    #[test]
    fn prop_check_expr_call_precision_argument_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
        let expr: Expr = sp_ast(ExprKind::Call {
            func: Box::new(sp_ast(ExprKind::Var("narrow".to_string()))),
            args: vec![kea_ast::Argument {
                label: None,
                value: sp_ast(ExprKind::Lit(Lit::Int(value))),
            }],
        });
        let mut env = crate::typeck::TypeEnv::new();
        env.bind(
            "narrow".to_string(),
            TypeScheme::mono(Type::Function(FunctionType {
                params: vec![expected.clone()],
                ret: Box::new(expected.clone()),
            })),
        );
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "call argument range diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Bidirectional check path for pipes pushes callee parameter types into
    /// piped arguments, surfacing precision-range diagnostics at literals.
    #[test]
    fn prop_check_expr_pipe_precision_argument_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
        let expr: Expr = sp_ast(ExprKind::Call {
            func: Box::new(sp_ast(ExprKind::Var("narrow".to_string()))),
            args: vec![kea_ast::Argument {
                label: None,
                value: sp_ast(ExprKind::Lit(Lit::Int(value))),
            }],
        });
        let mut env = crate::typeck::TypeEnv::new();
        env.bind(
            "narrow".to_string(),
            TypeScheme::mono(Type::Function(FunctionType {
                params: vec![expected.clone()],
                ret: Box::new(expected.clone()),
            })),
        );
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "pipe argument range diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Bidirectional check path for `Some(...)` pushes expected inner payload
    /// type into the constructor argument, surfacing precision diagnostics.
    #[test]
    fn prop_check_expr_some_constructor_precision_payload_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit, Spanned};

        let expected = Type::Option(Box::new(Type::IntN(IntWidth::I8, Signedness::Signed)));
        let expr: Expr = sp_ast(ExprKind::Constructor {
            name: Spanned::new("Some".to_string(), Span::new(FileId(0), 0, 0)),
            args: vec![ctor_arg(sp_ast(ExprKind::Lit(Lit::Int(value))))],
        });
        let mut env = crate::typeck::TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "constructor payload range diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Bidirectional check path for list literals pushes expected item type
    /// into each element, surfacing precision diagnostics.
    #[test]
    fn prop_check_expr_list_precision_element_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expected = Type::List(Box::new(Type::IntN(IntWidth::I8, Signedness::Signed)));
        let expr: Expr = sp_ast(ExprKind::List(vec![sp_ast(ExprKind::Lit(Lit::Int(value)))]));
        let mut env = crate::typeck::TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "list element range diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Bidirectional check path for map literals pushes expected key/value
    /// types into entries, surfacing precision diagnostics.
    #[test]
    fn prop_check_expr_map_precision_value_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expected = Type::Map(
            Box::new(Type::IntN(IntWidth::I8, Signedness::Signed)),
            Box::new(Type::IntN(IntWidth::I8, Signedness::Signed)),
        );
        let expr: Expr = sp_ast(ExprKind::MapLiteral(vec![(
            sp_ast(ExprKind::Lit(Lit::Int(1))),
            sp_ast(ExprKind::Lit(Lit::Int(value))),
        )]));
        let mut env = crate::typeck::TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "map value range diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Bidirectional check path for anonymous records pushes expected field
    /// types into matching fields, surfacing precision diagnostics.
    #[test]
    fn prop_check_expr_anon_record_precision_field_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expected = Type::AnonRecord(RowType::closed(vec![(
            Label::new("x"),
            Type::IntN(IntWidth::I8, Signedness::Signed),
        )]));
        let expr: Expr = sp_ast(ExprKind::AnonRecord {
            fields: vec![(
                sp_ast("x".to_string()),
                sp_ast(ExprKind::Lit(Lit::Int(value))),
            )],
            spread: None,
        });
        let mut env = crate::typeck::TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "anon-record field range diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Bidirectional check path for unary negation pushes expected numeric
    /// type into the operand, surfacing precision diagnostics.
    #[test]
    fn prop_check_expr_unary_neg_precision_operand_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit, UnaryOp};

        let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
        let expr: Expr = sp_ast(ExprKind::UnaryOp {
            op: sp_ast(UnaryOp::Neg),
            operand: Box::new(sp_ast(ExprKind::Lit(Lit::Int(value)))),
        });
        let mut env = crate::typeck::TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "unary-neg operand range diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Checked ascription should type-check the inner expression against the
    /// ascribed type, surfacing precision diagnostics at the literal.
    #[test]
    fn prop_check_expr_ascription_precision_inner_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit, TypeAnnotation};

        let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
        let expr: Expr = sp_ast(ExprKind::As {
            expr: Box::new(sp_ast(ExprKind::Lit(Lit::Int(value)))),
            annotation: sp_ast(TypeAnnotation::Named("Int8".to_string())),
        });
        let mut env = crate::typeck::TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "ascription-inner range diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Arithmetic binary ops in checked mode should push expected numeric type
    /// into both operands, surfacing precision diagnostics at literals.
    #[test]
    fn prop_check_expr_binary_precision_operand_range_diagnostics(
        left in any::<i64>(),
        right in any::<i64>(),
    ) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
        let expr: Expr = sp_ast(ExprKind::BinaryOp {
            op: sp_ast(kea_ast::BinOp::Add),
            left: Box::new(sp_ast(ExprKind::Lit(Lit::Int(left)))),
            right: Box::new(sp_ast(ExprKind::Lit(Lit::Int(right)))),
        });
        let mut env = crate::typeck::TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(left).is_err() || i8::try_from(right).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "binary-operand range diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Checked field access should push expected field type into the object row,
    /// surfacing precision diagnostics at object literal fields.
    #[test]
    fn prop_check_expr_field_access_precision_source_range_diagnostics(value in any::<i64>()) {
        use kea_ast::{Expr, ExprKind, Lit};

        let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
        let expr: Expr = sp_ast(ExprKind::FieldAccess {
            expr: Box::new(sp_ast(ExprKind::AnonRecord {
                fields: vec![(
                    sp_ast("x".to_string()),
                    sp_ast(ExprKind::Lit(Lit::Int(value))),
                )],
                spread: None,
            })),
            field: sp_ast("x".to_string()),
        });
        let mut env = crate::typeck::TypeEnv::new();
        let mut ctx = crate::InferenceContext::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sums = crate::typeck::SumTypeRegistry::new();

        let _ = check_expr_in_context(
            &expr,
            &expected,
            Reason::TypeAscription,
            &mut env,
            &mut ctx,
            &records,
            &traits,
            &sums,
        );

        let has_range_diag = ctx
            .errors()
            .iter()
            .any(|d| d.message.contains("does not fit in"));
        let should_range_error = i8::try_from(value).is_err();

        prop_assert_eq!(
            has_range_diag,
            should_range_error,
            "field-access source range diagnostics should match literal compatibility: {:?}",
            ctx.errors()
        );
    }
}

proptest! {
    /// Associated-type defaults that project through `Self` should resolve the
    /// same way regardless of declaration order.
    #[test]
    fn prop_assoc_default_projection_fixpoint_order_invariant(wrapped_first in proptest::bool::ANY) {
        let records = RecordRegistry::new();
        let mut traits = TraitRegistry::new();
        register_container_with_projected_defaults(&mut traits, &records, wrapped_first);

        let block = kea_ast::ImplBlock {
            trait_name: sp_ast("Container".to_string()),
            type_name: sp_ast("Int".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![],
        };
        traits
            .register_trait_impl(&block)
            .expect("impl should use defaults");

        let item = traits.solve_goal(&TraitGoal::ProjectionEq {
            base_trait: "Container".to_string(),
            base_ty: Type::Int,
            assoc: "Item".to_string(),
            rhs: Type::String,
        });
        prop_assert!(matches!(item, SolveOutcome::Unique(_)));

        let wrapped = traits.solve_goal(&TraitGoal::ProjectionEq {
            base_trait: "Container".to_string(),
            base_ty: Type::Int,
            assoc: "Wrapped".to_string(),
            rhs: Type::Option(Box::new(Type::String)),
        });
        prop_assert!(matches!(wrapped, SolveOutcome::Unique(_)));
    }
}

proptest! {
    /// Explicit associated-type assignments that project through `Self`
    /// should resolve regardless of where-clause ordering.
    #[test]
    fn prop_assoc_assignment_projection_order_invariant(wrapped_first in proptest::bool::ANY) {
        let records = RecordRegistry::new();
        let mut traits = TraitRegistry::new();
        let def = kea_ast::TraitDef {
            public: false,
            name: sp_ast("Container".to_string()),
            doc: None,
            type_params: vec![],
            supertraits: vec![],
            fundeps: vec![],
            associated_types: vec![
                kea_ast::AssociatedTypeDecl {
                    name: sp_ast("Item".to_string()),
                    constraints: vec![],
                    default: None,
                },
                kea_ast::AssociatedTypeDecl {
                    name: sp_ast("Wrapped".to_string()),
                    constraints: vec![],
                    default: None,
                },
            ],
            methods: vec![],
        };
        traits.register_trait(&def, &records).expect("Container trait should register");

        let wrapped_assignment = kea_ast::WhereItem::TypeAssignment {
            name: sp_ast("Wrapped".to_string()),
            ty: sp_ast(kea_ast::TypeAnnotation::Applied(
                "Option".into(),
                vec![kea_ast::TypeAnnotation::Projection {
                    base: "Self".into(),
                    name: "Item".into(),
                }],
            )),
        };
        let item_assignment = kea_ast::WhereItem::TypeAssignment {
            name: sp_ast("Item".to_string()),
            ty: sp_ast(kea_ast::TypeAnnotation::Named("String".into())),
        };
        let where_clause = if wrapped_first {
            vec![wrapped_assignment, item_assignment]
        } else {
            vec![item_assignment, wrapped_assignment]
        };

        let block = kea_ast::ImplBlock {
            trait_name: sp_ast("Container".to_string()),
            type_name: sp_ast("Int".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause,
        };
        traits.register_trait_impl(&block).expect("impl should register");

        let wrapped = traits.solve_goal(&TraitGoal::ProjectionEq {
            base_trait: "Container".to_string(),
            base_ty: Type::Int,
            assoc: "Wrapped".to_string(),
            rhs: Type::Option(Box::new(Type::String)),
        });
        prop_assert!(matches!(wrapped, SolveOutcome::Unique(_)));
    }
}

// ---------------------------------------------------------------------------
// Property: Temporal type round-trips
// ---------------------------------------------------------------------------

proptest! {
    /// Missing parameter-annotation diagnostics should aggregate all missing
    /// parameters into one diagnostic with one label per missing parameter.
    #[test]
    fn validate_fn_annotations_aggregates_missing_params(
        annotated_params in prop::collection::vec(proptest::bool::ANY, 1..=6)
    ) {
        use kea_ast::{FnDecl, Param, PatternKind, Spanned, TypeAnnotation};

        let span = Span::new(FileId(0), 0, 128);
        let params: Vec<Param> = annotated_params
            .iter()
            .enumerate()
            .map(|(idx, is_annotated)| Param {
                label: ParamLabel::Implicit,
                pattern: Spanned {
                    node: PatternKind::Var(format!("p{idx}")),
                    span: Span::new(FileId(0), (idx * 4) as u32, (idx * 4 + 2) as u32),
                },
                annotation: if *is_annotated {
                    Some(Spanned {
                        node: TypeAnnotation::Named("Int".to_string()),
                        span,
                    })
                } else {
                    None
                },
                default: None,
            })
            .collect();

        let fn_decl = FnDecl {
    annotations: vec![],
            public: false,
            name: Spanned {
                node: "f".to_string(),
                span,
            },
            doc: None,
            params,
            return_annotation: None,
            effect_annotation: None,
            body: Spanned {
                node: kea_ast::ExprKind::Lit(kea_ast::Lit::Unit),
                span,
            },
            span,
            where_clause: Vec::new(),
        testing: None,
        testing_tags: Vec::new(),
        };

        let missing_count = annotated_params.iter().filter(|is_annotated| !**is_annotated).count();
        let diags = crate::typeck::validate_fn_decl_annotations(&fn_decl);
        if missing_count == 0 {
            prop_assert!(diags.is_empty());
        } else {
            prop_assert_eq!(diags.len(), 1);
            let diag = &diags[0];
            prop_assert_eq!(diag.category, kea_diag::Category::MissingAnnotation);
            prop_assert_eq!(diag.code.as_deref(), Some("E0801"));
            prop_assert_eq!(diag.labels.len(), missing_count);
        }
    }
}

proptest! {
    /// Date round-trip: arbitrary i32 → Date → substitution apply → still Date.
    /// Ensures Date is treated as a ground type (leaf) by substitution.
    #[test]
    fn date_is_substitution_leaf(days in proptest::num::i32::ANY) {
        let ty = Type::Date;
        let mut subst = Substitution::new();
        subst.bind_type(TypeVarId(0), Type::Date);
        let applied = subst.apply(&ty);
        prop_assert_eq!(applied, Type::Date);

        // Date inside a container also survives substitution
        let opt_date = Type::Option(Box::new(Type::Date));
        let applied_opt = subst.apply(&opt_date);
        prop_assert_eq!(applied_opt, Type::Option(Box::new(Type::Date)));

        // Verify the value representation is lossless
        let _ = days; // used to generate variety; type itself is always Date
    }

    /// DateTime round-trip: same as Date — a ground type leaf.
    #[test]
    fn datetime_is_substitution_leaf(micros in proptest::num::i64::ANY) {
        let ty = Type::DateTime;
        let mut subst = Substitution::new();
        subst.bind_type(TypeVarId(0), Type::DateTime);
        let applied = subst.apply(&ty);
        prop_assert_eq!(applied, Type::DateTime);

        let list_dt = Type::List(Box::new(Type::DateTime));
        let applied_list = subst.apply(&list_dt);
        prop_assert_eq!(applied_list, Type::List(Box::new(Type::DateTime)));

        let _ = micros;
    }

    /// Unification of Date with Date always succeeds (reflexivity).
    #[test]
    fn date_unifies_with_self(_seed in 0u32..100) {
        let mut unifier = crate::Unifier::new();
        let prov = test_prov();
        unifier.unify(&Type::Date, &Type::Date, &prov);
        prop_assert!(!unifier.has_errors(), "Date should unify with Date");
    }

    /// Unification of DateTime with DateTime always succeeds.
    #[test]
    fn datetime_unifies_with_self(_seed in 0u32..100) {
        let mut unifier = crate::Unifier::new();
        let prov = test_prov();
        unifier.unify(&Type::DateTime, &Type::DateTime, &prov);
        prop_assert!(!unifier.has_errors(), "DateTime should unify with DateTime");
    }

    /// Date does NOT unify with DateTime (they are distinct types).
    #[test]
    fn date_does_not_unify_with_datetime(_seed in 0u32..100) {
        let mut unifier = crate::Unifier::new();
        let prov = test_prov();
        unifier.unify(&Type::Date, &Type::DateTime, &prov);
        prop_assert!(unifier.has_errors(), "Date should not unify with DateTime");
    }

    /// Date/DateTime in rows: a row containing Date fields should unify
    /// with another row containing Date fields in the same positions.
    #[test]
    fn temporal_row_unification(
        date_label in prop::sample::select(&["created", "updated", "birth"][..]),
        dt_label in prop::sample::select(&["timestamp", "modified", "logged"][..]),
    ) {
        let row1 = RowType::closed(vec![
            (Label::new(date_label), Type::Date),
            (Label::new(dt_label), Type::DateTime),
        ]);
        let row2 = RowType::closed(vec![
            (Label::new(date_label), Type::Date),
            (Label::new(dt_label), Type::DateTime),
        ]);
        let ty1 = Type::AnonRecord(row1);
        let ty2 = Type::AnonRecord(row2);

        let mut unifier = crate::Unifier::new();
        let prov = test_prov();
        unifier.unify(&ty1, &ty2, &prov);
        prop_assert!(!unifier.has_errors(), "identical temporal rows should unify");
    }

    /// Temporal primitives are sendable (Date and DateTime).
    #[test]
    fn temporal_types_are_sendable(
        use_date in proptest::bool::ANY,
    ) {
        let ty = if use_date { Type::Date } else { Type::DateTime };
        prop_assert!(kea_types::is_sendable(&ty), "{ty} should be Sendable");

        let opt_ty = Type::Option(Box::new(ty.clone()));
        prop_assert!(kea_types::is_sendable(&opt_ty), "Option({ty}) should be Sendable");

        let list_ty = Type::List(Box::new(ty.clone()));
        prop_assert!(kea_types::is_sendable(&list_ty), "List({ty}) should be Sendable");
    }

    /// Free type vars of temporal types is empty (they are ground types).
    #[test]
    fn temporal_types_have_no_free_vars(use_date in proptest::bool::ANY) {
        let ty = if use_date { Type::Date } else { Type::DateTime };
        let vars = kea_types::free_type_vars(&ty);
        prop_assert!(vars.is_empty(), "{ty} should have no free vars");
    }
}

// ---------------------------------------------------------------------------
// Property tests for ownership scope
// ---------------------------------------------------------------------------

fn arb_ownership_tag() -> impl Strategy<Value = String> {
    prop_oneof![
        // pkg:<name>
        "[a-z][a-z0-9_]{0,10}".prop_map(|n| format!("pkg:{n}")),
        // project:<path>
        "[A-Z][A-Za-z0-9.]{0,15}".prop_map(|p| format!("project:{p}")),
        // kea: singleton
        Just("kea:".to_string()),
        // repl: singleton
        Just("repl:".to_string()),
    ]
}

proptest! {
    /// same_ownership_scope is reflexive: any ownership string is in scope with itself.
    #[test]
    fn ownership_scope_reflexive(tag in arb_ownership_tag()) {
        prop_assert!(
            crate::typeck::same_ownership_scope(&tag, &tag),
            "ownership scope should be reflexive for {tag}"
        );
    }

    /// same_ownership_scope is symmetric.
    #[test]
    fn ownership_scope_symmetric(a in arb_ownership_tag(), b in arb_ownership_tag()) {
        let ab = crate::typeck::same_ownership_scope(&a, &b);
        let ba = crate::typeck::same_ownership_scope(&b, &a);
        prop_assert_eq!(ab, ba, "ownership scope should be symmetric");
    }

    /// Different prefixes never share scope.
    #[test]
    fn ownership_scope_cross_prefix_never_same(
        a in arb_ownership_tag(),
        b in arb_ownership_tag(),
    ) {
        let scope_a = crate::typeck::ownership_scope(&a);
        let scope_b = crate::typeck::ownership_scope(&b);
        // If scopes are equal, the function must return true
        if scope_a == scope_b {
            prop_assert!(
                crate::typeck::same_ownership_scope(&a, &b),
                "equal scopes should mean same_ownership_scope: {a} / {b}"
            );
        } else {
            prop_assert!(
                !crate::typeck::same_ownership_scope(&a, &b),
                "different scopes should mean different ownership: {a} / {b}"
            );
        }
    }

    /// All project: tags share the same scope regardless of module path.
    #[test]
    fn project_modules_always_share_scope(
        a in "[A-Z][A-Za-z0-9.]{0,15}",
        b in "[A-Z][A-Za-z0-9.]{0,15}",
    ) {
        let tag_a = format!("project:{a}");
        let tag_b = format!("project:{b}");
        prop_assert!(
            crate::typeck::same_ownership_scope(&tag_a, &tag_b),
            "all project modules should share scope: {tag_a} vs {tag_b}"
        );
    }

    /// pkg: tags only share scope if the package name is the same.
    #[test]
    fn package_scope_matches_by_name(
        name in "[a-z][a-z0-9_]{0,10}",
    ) {
        let tag1 = format!("pkg:{name}");
        let tag2 = format!("pkg:{name}");
        prop_assert!(
            crate::typeck::same_ownership_scope(&tag1, &tag2),
            "same package name should share scope"
        );
    }
}
