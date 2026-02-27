//! Tests for expression-level type inference and let-generalization.
//!
//! Each test constructs an AST by hand and checks the inferred type.
//! This is verbose but precise — we know exactly what we're testing.

use std::collections::BTreeMap;

use kea_ast::*;
use kea_types::*;

use crate::typeck::*;
use crate::{Category, InferenceContext, Provenance, Reason, Unifier};

// ---------------------------------------------------------------------------
// Helpers for constructing AST nodes
// ---------------------------------------------------------------------------

fn s() -> Span {
    Span::new(FileId(0), 0, 1)
}

fn sp<T>(node: T) -> Spanned<T> {
    Spanned::new(node, s())
}

fn lit_int(n: i64) -> Expr {
    sp(ExprKind::Lit(Lit::Int(n)))
}

fn lit_float(n: f64) -> Expr {
    sp(ExprKind::Lit(Lit::Float(n)))
}

fn lit_bool(b: bool) -> Expr {
    sp(ExprKind::Lit(Lit::Bool(b)))
}

fn lit_str(s_val: &str) -> Expr {
    sp(ExprKind::Lit(Lit::String(s_val.to_string())))
}

fn decimal(precision: i64, scale: i64) -> Type {
    Type::Decimal {
        precision: Dim::Known(precision),
        scale: Dim::Known(scale),
    }
}

fn none_expr() -> Expr {
    sp(ExprKind::None)
}

fn lit_unit() -> Expr {
    sp(ExprKind::Lit(Lit::Unit))
}

fn var(name: &str) -> Expr {
    sp(ExprKind::Var(name.to_string()))
}

fn unary(op: UnaryOp, operand: Expr) -> Expr {
    sp(ExprKind::UnaryOp {
        op: sp(op),
        operand: Box::new(operand),
    })
}

fn let_bind(name: &str, value: Expr) -> Expr {
    sp(ExprKind::Let {
        pattern: sp(PatternKind::Var(name.to_string())),
        annotation: None,
        value: Box::new(value),
    })
}

fn lambda(params: &[&str], body: Expr) -> Expr {
    sp(ExprKind::Lambda {
        params: params
            .iter()
            .map(|name| Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var(name.to_string())),
                annotation: None,
                default: None,
            })
            .collect(),
        body: Box::new(body),
        return_annotation: None,
    })
}

fn call(func: Expr, args: Vec<Expr>) -> Expr {
    sp(ExprKind::Call {
        func: Box::new(func),
        args: args
            .into_iter()
            .map(|value| Argument { label: None, value })
            .collect(),
    })
}

fn call_with_args(func: Expr, args: Vec<Argument>) -> Expr {
    sp(ExprKind::Call {
        func: Box::new(func),
        args,
    })
}

fn labeled_arg(label: &str, value: Expr) -> Argument {
    Argument {
        label: Some(sp(label.to_string())),
        value,
    }
}

fn if_expr(cond: Expr, then_b: Expr, else_b: Option<Expr>) -> Expr {
    sp(ExprKind::If {
        condition: Box::new(cond),
        then_branch: Box::new(then_b),
        else_branch: else_b.map(Box::new),
    })
}

fn binop(op: BinOp, left: Expr, right: Expr) -> Expr {
    sp(ExprKind::BinaryOp {
        op: sp(op),
        left: Box::new(left),
        right: Box::new(right),
    })
}

fn range_expr(start: Expr, end: Expr, inclusive: bool) -> Expr {
    sp(ExprKind::Range {
        start: Box::new(start),
        end: Box::new(end),
        inclusive,
    })
}

fn tuple(elems: Vec<Expr>) -> Expr {
    sp(ExprKind::Tuple(elems))
}

fn list(elems: Vec<Expr>) -> Expr {
    sp(ExprKind::List(elems))
}

fn map_literal(pairs: Vec<(Expr, Expr)>) -> Expr {
    sp(ExprKind::MapLiteral(pairs))
}

fn anon_record(fields: Vec<(&str, Expr)>) -> Expr {
    sp(ExprKind::AnonRecord {
        fields: fields
            .into_iter()
            .map(|(name, expr)| (sp(name.to_string()), expr))
            .collect(),
        spread: None,
    })
}

fn field_access(expr: Expr, field: &str) -> Expr {
    sp(ExprKind::FieldAccess {
        expr: Box::new(expr),
        field: sp(field.to_string()),
    })
}

fn block(exprs: Vec<Expr>) -> Expr {
    sp(ExprKind::Block(exprs))
}

fn stream_block(body: Expr) -> Expr {
    sp(ExprKind::StreamBlock {
        body: Box::new(body),
        buffer_size: 32,
    })
}

fn yield_expr(value: Expr) -> Expr {
    sp(ExprKind::Yield {
        value: Box::new(value),
    })
}

fn yield_from_expr(source: Expr) -> Expr {
    sp(ExprKind::YieldFrom {
        source: Box::new(source),
    })
}

fn for_expr(clauses: Vec<ForClause>, body: Expr) -> Expr {
    sp(ExprKind::For(ForExpr {
        clauses,
        body: Box::new(body),
        into_type: None,
    }))
}

fn for_expr_into(clauses: Vec<ForClause>, body: Expr, into_name: &str) -> Expr {
    sp(ExprKind::For(ForExpr {
        clauses,
        body: Box::new(body),
        into_type: Some(sp(TypeAnnotation::Named(into_name.to_string()))),
    }))
}

fn for_gen(pattern: Pattern, source: Expr) -> ForClause {
    ForClause::Generator {
        pattern,
        source: Box::new(source),
    }
}

fn for_guard(guard: Expr) -> ForClause {
    ForClause::Guard(Box::new(guard))
}

fn has_unique_impl(traits: &TraitRegistry, trait_name: &str, ty: Type) -> bool {
    matches!(
        traits.solve_goal(&TraitGoal::Implements {
            trait_name: trait_name.to_string(),
            ty,
        }),
        SolveOutcome::Unique(_)
    )
}

fn use_expr(pattern: Option<Pattern>, rhs: Expr) -> Expr {
    sp(ExprKind::Use(UseExpr {
        pattern,
        rhs: Box::new(rhs),
    }))
}

fn handle_clause(effect: &str, operation: &str, args: Vec<Pattern>, body: Expr) -> HandleClause {
    HandleClause {
        effect: sp(effect.to_string()),
        operation: sp(operation.to_string()),
        args,
        body,
        span: s(),
    }
}

fn handle_expr(handled: Expr, clauses: Vec<HandleClause>, then_clause: Option<Expr>) -> Expr {
    sp(ExprKind::Handle {
        expr: Box::new(handled),
        clauses,
        then_clause: then_clause.map(Box::new),
    })
}

fn resume(value: Expr) -> Expr {
    sp(ExprKind::Resume {
        value: Box::new(value),
    })
}

fn spawn_expr(value: Expr) -> Expr {
    sp(ExprKind::Spawn {
        value: Box::new(value),
        config: None,
    })
}

fn await_expr(expr: Expr, safe: bool) -> Expr {
    sp(ExprKind::Await {
        expr: Box::new(expr),
        safe,
    })
}

fn actor_send(actor: Expr, method: &str, args: Vec<Expr>) -> Expr {
    sp(ExprKind::ActorSend {
        actor: Box::new(actor),
        method: sp(method.to_string()),
        args,
        safe: false,
    })
}

fn actor_try_send(actor: Expr, method: &str, args: Vec<Expr>) -> Expr {
    sp(ExprKind::ActorSend {
        actor: Box::new(actor),
        method: sp(method.to_string()),
        args,
        safe: true,
    })
}

fn actor_call(actor: Expr, method: &str, args: Vec<Expr>) -> Expr {
    sp(ExprKind::ActorCall {
        actor: Box::new(actor),
        method: sp(method.to_string()),
        args,
        safe: false,
    })
}

fn actor_call_safe(actor: Expr, method: &str, args: Vec<Expr>) -> Expr {
    sp(ExprKind::ActorCall {
        actor: Box::new(actor),
        method: sp(method.to_string()),
        args,
        safe: true,
    })
}

fn traits_with_actor() -> TraitRegistry {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let actor_trait = kea_ast::TraitDef {
        public: true,
        name: sp("Actor".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits
        .register_trait(&actor_trait, &records)
        .expect("register Actor trait");
    traits
        .register_trait_impl(&kea_ast::ImplBlock {
            trait_name: sp("Actor".to_string()),
            type_name: sp("Int".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![],
        })
        .expect("register Actor for Int");
    traits
}

fn apply_first_arg(left: Expr, right: Expr) -> Expr {
    match right.node {
        ExprKind::Call { func, args } => {
            let mut combined_args = vec![Argument {
                label: None,
                value: left,
            }];
            combined_args.extend(args);
            sp(ExprKind::Call {
                func,
                args: combined_args,
            })
        }
        _ => call(right, vec![left]),
    }
}

fn ascribe(expr: Expr, annotation: TypeAnnotation) -> Expr {
    sp(ExprKind::As {
        expr: Box::new(expr),
        annotation: sp(annotation),
    })
}

fn constructor(name: &str, args: Vec<Expr>) -> Expr {
    sp(ExprKind::Constructor {
        name: sp(name.to_string()),
        args: args
            .into_iter()
            .map(|value| Argument { label: None, value })
            .collect(),
    })
}

fn ctor_pat_arg(pattern: Pattern) -> ConstructorFieldPattern {
    ConstructorFieldPattern {
        name: None,
        pattern,
    }
}

fn constructor_pattern(name: &str, args: Vec<Pattern>) -> Pattern {
    sp(PatternKind::Constructor {
        name: name.to_string(),
        args: args.into_iter().map(ctor_pat_arg).collect(),
        rest: false,
        qualifier: None,
    })
}

fn variant_field(ty: TypeAnnotation) -> VariantField {
    VariantField {
        annotations: vec![],
        name: None,
        ty: sp(ty),
        span: s(),
    }
}

fn ann(name: &str, args: Vec<Argument>) -> kea_ast::Annotation {
    kea_ast::Annotation {
        name: sp(name.to_string()),
        args,
        span: s(),
    }
}

fn ann_arg(value: Expr) -> Argument {
    Argument { label: None, value }
}

fn effect_row_annotation(
    effects: Vec<(&str, Option<&str>)>,
    rest: Option<&str>,
) -> EffectAnnotation {
    EffectAnnotation::Row(EffectRowAnnotation {
        effects: effects
            .into_iter()
            .map(|(name, payload)| EffectRowItem {
                name: name.to_string(),
                payload: payload.map(str::to_string),
            })
            .collect(),
        rest: rest.map(str::to_string),
    })
}

fn register_hkt_for_use_for_traits(traits: &mut TraitRegistry, records: &RecordRegistry) {
    let bind_trait = TraitDef {
        public: false,
        name: sp("Bind".to_string()),
        doc: None,
        type_params: vec![TraitTypeParam {
            name: sp("F".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&bind_trait, records).unwrap();

    let comprehensible_trait = TraitDef {
        public: false,
        name: sp("Comprehensible".to_string()),
        doc: None,
        type_params: vec![TraitTypeParam {
            name: sp("F".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![sp("Bind".to_string())],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits
        .register_trait(&comprehensible_trait, records)
        .unwrap();

    let applicative_trait = TraitDef {
        public: false,
        name: sp("Applicative".to_string()),
        doc: None,
        type_params: vec![TraitTypeParam {
            name: sp("F".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![sp("Comprehensible".to_string())],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&applicative_trait, records).unwrap();

    for constructor in ["List", "Option", "Stream"] {
        traits
            .register_trait_impl(&ImplBlock {
                trait_name: sp("Bind".to_string()),
                type_name: sp(constructor.to_string()),
                type_params: vec![],
                methods: vec![],
                control_type: None,
                where_clause: vec![],
            })
            .unwrap();
        traits
            .register_trait_impl(&ImplBlock {
                trait_name: sp("Comprehensible".to_string()),
                type_name: sp(constructor.to_string()),
                type_params: vec![],
                methods: vec![],
                control_type: None,
                where_clause: vec![],
            })
            .unwrap();
        traits
            .register_trait_impl(&ImplBlock {
                trait_name: sp("Applicative".to_string()),
                type_name: sp(constructor.to_string()),
                type_params: vec![],
                methods: vec![],
                control_type: None,
                where_clause: vec![],
            })
            .unwrap();
    }

    for trait_name in ["Bind", "Comprehensible", "Applicative"] {
        traits
            .register_trait_impl(&ImplBlock {
                trait_name: sp(trait_name.to_string()),
                type_name: sp("Result".to_string()),
                type_params: vec![sp("_".to_string()), sp("e".to_string())],
                methods: vec![],
                control_type: None,
                where_clause: vec![],
            })
            .unwrap();
    }
}

fn infer(expr: &Expr) -> (Type, Unifier) {
    let mut env = TypeEnv::new();
    let mut unifier = Unifier::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();
    let ty = infer_and_resolve(expr, &mut env, &mut unifier, &records, &traits, &sum_types);
    (ty, unifier)
}

fn infer_with_env(expr: &Expr, env: &mut TypeEnv) -> (Type, Unifier) {
    let mut unifier = Unifier::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();
    let ty = infer_and_resolve(expr, env, &mut unifier, &records, &traits, &sum_types);
    (ty, unifier)
}

fn infer_with_records(expr: &Expr, records: &RecordRegistry) -> (Type, Unifier) {
    let mut env = TypeEnv::new();
    let mut unifier = Unifier::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, records);
    let sum_types = SumTypeRegistry::new();
    let ty = infer_and_resolve(expr, &mut env, &mut unifier, records, &traits, &sum_types);
    (ty, unifier)
}

fn infer_with_context(expr: &Expr) -> (Type, InferenceContext) {
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();
    let ty = infer_and_resolve_in_context(expr, &mut env, &mut ctx, &records, &traits, &sum_types);
    (ty, ctx)
}

fn make_record_def(name: &str, fields: Vec<(&str, TypeAnnotation)>) -> RecordDef {
    RecordDef {
        annotations: vec![],
        public: false,
        name: sp(name.to_string()),
        doc: None,
        params: Vec::new(),
        derives: Vec::new(),
        fields: fields
            .into_iter()
            .map(|(n, ann)| (sp(n.to_string()), ann))
            .collect(),
        field_annotations: vec![],
    }
}

fn make_param_record_def(
    name: &str,
    params: Vec<&str>,
    fields: Vec<(&str, TypeAnnotation)>,
) -> RecordDef {
    RecordDef {
        annotations: vec![],
        public: false,
        name: sp(name.to_string()),
        doc: None,
        params: params.into_iter().map(ToString::to_string).collect(),
        derives: Vec::new(),
        fields: fields
            .into_iter()
            .map(|(n, ann)| (sp(n.to_string()), ann))
            .collect(),
        field_annotations: vec![],
    }
}

fn make_alias_def(name: &str, params: Vec<&str>, target: TypeAnnotation) -> AliasDecl {
    AliasDecl {
        public: false,
        name: sp(name.to_string()),
        doc: None,
        params: params.into_iter().map(ToString::to_string).collect(),
        target: sp(target),
    }
}

fn make_opaque_def(
    name: &str,
    params: Vec<&str>,
    target: TypeAnnotation,
    derives: Vec<&str>,
) -> OpaqueTypeDef {
    OpaqueTypeDef {
        public: false,
        name: sp(name.to_string()),
        doc: None,
        params: params.into_iter().map(ToString::to_string).collect(),
        target: sp(target),
        derives: derives
            .into_iter()
            .map(|trait_name| sp(trait_name.to_string()))
            .collect(),
    }
}

fn make_type_def(
    name: &str,
    params: Vec<&str>,
    variants: Vec<(&str, Vec<TypeAnnotation>)>,
) -> TypeDef {
    TypeDef {
        annotations: vec![],
        public: false,
        name: sp(name.to_string()),
        doc: None,
        params: params.into_iter().map(ToString::to_string).collect(),
        variants: variants
            .into_iter()
            .map(|(variant_name, fields)| TypeVariant {
                annotations: vec![],
                name: sp(variant_name.to_string()),
                fields: fields.into_iter().map(variant_field).collect(),
                where_clause: vec![],
            })
            .collect(),
        derives: vec![],
    }
}

#[test]
fn infer_and_resolve_context_entrypoint_matches_unifier_entrypoint() {
    let expr = block(vec![
        let_bind("x", lit_int(1)),
        binop(BinOp::Add, var("x"), lit_int(2)),
    ]);
    let (unifier_ty, unifier) = infer(&expr);
    let (ctx_ty, ctx) = infer_with_context(&expr);

    assert_eq!(unifier_ty, Type::Int);
    assert_eq!(ctx_ty, unifier_ty);
    assert_eq!(ctx.has_errors(), unifier.has_errors());
}

#[test]
fn check_expr_context_entrypoint_applies_expected_type_constraint() {
    let expr = binop(BinOp::Add, lit_int(1), lit_int(2));
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let checked = check_expr_in_context(
        &expr,
        &Type::Int,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );
    assert_eq!(ctx.substitution().apply(&checked), Type::Int);
    assert!(
        !ctx.has_errors(),
        "expected check_expr_in_context success, got {:?}",
        ctx.errors()
    );

    let mut mismatch_env = TypeEnv::new();
    let mut mismatch_ctx = InferenceContext::new();
    let mismatch = check_expr_in_context(
        &expr,
        &Type::String,
        Reason::TypeAscription,
        &mut mismatch_env,
        &mut mismatch_ctx,
        &records,
        &traits,
        &sum_types,
    );
    assert_eq!(mismatch_ctx.substitution().apply(&mismatch), Type::Int);
    assert!(
        mismatch_ctx.has_errors(),
        "expected mismatch diagnostics for check_expr_in_context"
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_if_branches() {
    let expr = if_expr(lit_bool(true), lit_int(200), Some(lit_int(1)));
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked if-branch, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_cond_arms() {
    let expr = cond_expr(vec![
        cond_arm(lit_bool(true), lit_int(200)),
        cond_wildcard_arm(lit_int(1)),
    ]);
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked cond arm, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_case_arms() {
    let expr = case_expr(
        none_expr(),
        vec![
            arm(pat_constructor("None", vec![]), lit_int(200)),
            arm(pat_constructor("Some", vec![pat_var("n")]), var("n")),
        ],
    );
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked case arm, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_call_arguments() {
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let expr = call(var("narrow"), vec![lit_int(200)]);
    let mut env = TypeEnv::new();
    env.bind(
        "narrow".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![expected.clone()],
            ret: Box::new(expected.clone()),
            effects: EffectRow::pure(),
        })),
    );
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked call arg, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_left_arg_application_arguments() {
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let expr = apply_first_arg(lit_int(200), var("narrow"));
    let mut env = TypeEnv::new();
    env.bind(
        "narrow".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![expected.clone()],
            ret: Box::new(expected.clone()),
            effects: EffectRow::pure(),
        })),
    );
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked left-arg application arg, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_some_constructor_payload() {
    let expected = Type::Option(Box::new(Type::IntN(IntWidth::I8, Signedness::Signed)));
    let expr = constructor("Some", vec![lit_int(200)]);
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked constructor payload, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_err_constructor_payload() {
    let expected = Type::Result(
        Box::new(Type::Int),
        Box::new(Type::IntN(IntWidth::I8, Signedness::Signed)),
    );
    let expr = constructor("Err", vec![lit_int(200)]);
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked result constructor payload, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_list_elements() {
    let expected = Type::List(Box::new(Type::IntN(IntWidth::I8, Signedness::Signed)));
    let expr = list(vec![lit_int(200)]);
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked list element, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_tuple_elements() {
    let expected = Type::Tuple(vec![
        Type::IntN(IntWidth::I8, Signedness::Signed),
        Type::IntN(IntWidth::I8, Signedness::Signed),
    ]);
    let expr = tuple(vec![lit_int(1), lit_int(200)]);
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked tuple element, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_map_entries() {
    let expected = Type::Map(
        Box::new(Type::IntN(IntWidth::I8, Signedness::Signed)),
        Box::new(Type::IntN(IntWidth::I8, Signedness::Signed)),
    );
    let expr = map_literal(vec![(lit_int(1), lit_int(200))]);
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked map entry, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_anon_record_fields() {
    let expected = Type::AnonRecord(RowType::closed(vec![(
        Label::new("x"),
        Type::IntN(IntWidth::I8, Signedness::Signed),
    )]));
    let expr = anon_record(vec![("x", lit_int(200))]);
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked anon record field, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_unary_neg_operand() {
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let expr = unary(UnaryOp::Neg, lit_int(200));
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked unary neg operand, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_through_ascription_inner() {
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let expr = sp(ExprKind::As {
        expr: Box::new(lit_int(200)),
        annotation: sp(TypeAnnotation::Named("Int8".to_string())),
    });
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked ascription inner value, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_into_binary_operands() {
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let expr = binop(BinOp::Add, lit_int(200), lit_int(1));
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from checked binary operand, got {:?}",
        ctx.errors()
    );
}

#[test]
fn check_expr_context_pushes_expected_precision_through_field_access() {
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let expr = field_access(anon_record(vec![("x", lit_int(200))]), "x");
    let mut env = TypeEnv::new();
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let sum_types = SumTypeRegistry::new();

    let _ = check_expr_in_context(
        &expr,
        &expected,
        Reason::TypeAscription,
        &mut env,
        &mut ctx,
        &records,
        &traits,
        &sum_types,
    );

    assert!(
        ctx.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic through checked field access, got {:?}",
        ctx.errors()
    );
}

#[test]
fn alias_named_expands_in_annotations() {
    let mut records = RecordRegistry::new();
    records
        .register_alias(&make_alias_def(
            "UserId",
            vec![],
            TypeAnnotation::Named("Int".to_string()),
        ))
        .expect("alias registration");

    let ty = resolve_annotation(&TypeAnnotation::Named("UserId".to_string()), &records, None)
        .expect("alias should resolve");
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_named_record_construction_uses_checked_field_precision() {
    let mut records = RecordRegistry::new();
    records
        .register(&make_record_def(
            "Small",
            vec![("value", TypeAnnotation::Named("Int8".to_string()))],
        ))
        .expect("record registration");

    let expr = named_record("Small", vec![("value", lit_int(200))]);
    let (_ty, u) = infer_with_records(&expr, &records);
    assert!(
        u.errors()
            .iter()
            .any(|d| d.message.contains("does not fit in")),
        "expected precision-range diagnostic from named record field, got {:?}",
        u.errors()
    );
}

#[test]
fn alias_parametric_expands_in_annotations() {
    let mut records = RecordRegistry::new();
    records
        .register_alias(&make_alias_def(
            "Pair",
            vec!["a", "b"],
            TypeAnnotation::Tuple(vec![
                TypeAnnotation::Named("a".to_string()),
                TypeAnnotation::Named("b".to_string()),
            ]),
        ))
        .expect("alias registration");

    let ty = resolve_annotation(
        &TypeAnnotation::Applied(
            "Pair".to_string(),
            vec![
                TypeAnnotation::Named("Int".to_string()),
                TypeAnnotation::Named("Bool".to_string()),
            ],
        ),
        &records,
        None,
    )
    .expect("alias should resolve");
    assert_eq!(ty, Type::Tuple(vec![Type::Int, Type::Bool]));
}

#[test]
fn alias_forall_expands_in_annotations() {
    let mut records = RecordRegistry::new();
    records
        .register_alias(&make_alias_def(
            "Endo",
            vec![],
            TypeAnnotation::Forall {
                type_vars: vec!["a".to_string()],
                ty: Box::new(TypeAnnotation::Function(
                    vec![TypeAnnotation::Named("a".to_string())],
                    Box::new(TypeAnnotation::Named("a".to_string())),
                )),
            },
        ))
        .expect("alias registration");

    let ty = resolve_annotation(&TypeAnnotation::Named("Endo".to_string()), &records, None)
        .expect("forall alias should resolve");
    let Type::Forall(scheme) = ty else {
        panic!("expected forall type alias");
    };
    assert_eq!(scheme.type_vars.len(), 1);
    let bound = scheme.type_vars[0];
    match &scheme.ty {
        Type::Function(ft) => {
            assert_eq!(ft.params, vec![Type::Var(bound)]);
            assert_eq!(ft.ret.as_ref(), &Type::Var(bound));
        }
        other => panic!("expected function inside forall, got {other:?}"),
    }
}

#[test]
fn alias_resolution_is_unifier_independent() {
    let mut records = RecordRegistry::new();
    records
        .register_alias(&make_alias_def(
            "UserId",
            vec![],
            TypeAnnotation::Named("Int".to_string()),
        ))
        .expect("alias registration");

    let ty = resolve_annotation(&TypeAnnotation::Named("UserId".to_string()), &records, None)
        .expect("alias should resolve");
    assert_eq!(ty, Type::Int);

    // Alias expansion is declaration-time canonicalization and must not
    // consume fresh inference variables from an unrelated Unifier.
    let mut unifier = Unifier::with_var_offsets(0, 0, 0);
    assert_eq!(unifier.fresh_type_var(), TypeVarId(0));
    assert_eq!(unifier.fresh_row_var(), RowVarId(0));
}

#[test]
fn alias_cycle_is_rejected() {
    let mut records = RecordRegistry::new();
    records
        .register_alias(&make_alias_def(
            "A",
            vec![],
            TypeAnnotation::Named("B".to_string()),
        ))
        .expect("first alias registration");
    let err = records
        .register_alias(&make_alias_def(
            "B",
            vec![],
            TypeAnnotation::Named("A".to_string()),
        ))
        .expect_err("cyclic aliases should fail");
    assert!(
        err.message.contains("cyclic alias definition"),
        "unexpected error: {}",
        err.message
    );
}

#[test]
fn effect_row_alias_expands_in_declared_effect_contract_validation() {
    let mut records = RecordRegistry::new();
    records
        .register_alias(&make_alias_def(
            "DbEffects",
            vec![],
            TypeAnnotation::EffectRow(EffectRowAnnotation {
                effects: vec![EffectRowItem {
                    name: "IO".to_string(),
                    payload: None,
                }],
                rest: None,
            }),
        ))
        .expect("alias registration");

    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(effect_row_annotation(vec![("DbEffects", None)], None)));

    let env = TypeEnv::new();
    assert!(
        validate_declared_fn_effect_with_env_and_records(
            &fn_decl,
            Effects::impure(),
            &env,
            &records
        )
        .is_ok()
    );
}

#[test]
fn open_effect_row_alias_is_supported_in_contract_validation() {
    let mut records = RecordRegistry::new();
    records
        .register_alias(&make_alias_def(
            "WithDb",
            vec![],
            TypeAnnotation::EffectRow(EffectRowAnnotation {
                effects: vec![EffectRowItem {
                    name: "IO".to_string(),
                    payload: None,
                }],
                rest: Some("e".to_string()),
            }),
        ))
        .expect("alias registration");

    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(effect_row_annotation(vec![("WithDb", None)], None)));
    let env = TypeEnv::new();
    assert!(
        validate_declared_fn_effect_with_env_and_records(
            &fn_decl,
            Effects::impure(),
            &env,
            &records
        )
        .is_ok()
    );
}

#[test]
fn opaque_named_resolves_as_nominal_type() {
    let mut records = RecordRegistry::new();
    records
        .register_opaque(&make_opaque_def(
            "UserId",
            vec![],
            TypeAnnotation::Named("Int".to_string()),
            vec![],
        ))
        .expect("opaque registration");

    let ty = resolve_annotation(&TypeAnnotation::Named("UserId".to_string()), &records, None)
        .expect("opaque should resolve");
    assert_eq!(
        ty,
        Type::Opaque {
            name: "UserId".to_string(),
            params: vec![],
        }
    );
}

#[test]
fn infer_opaque_constructor_and_value_accessor() {
    let mut records = RecordRegistry::new();
    records
        .register_opaque(&make_opaque_def(
            "UserId",
            vec![],
            TypeAnnotation::Named("Int".to_string()),
            vec![],
        ))
        .expect("opaque registration");

    let constructor_expr = constructor("UserId", vec![lit_int(42)]);
    let (ctor_ty, ctor_unifier) = infer_with_records(&constructor_expr, &records);
    assert!(!ctor_unifier.has_errors());
    assert_eq!(
        ctor_ty,
        Type::Opaque {
            name: "UserId".to_string(),
            params: vec![],
        }
    );

    let value_expr = sp(ExprKind::FieldAccess {
        expr: Box::new(constructor_expr),
        field: sp("value".to_string()),
    });
    let (value_ty, value_unifier) = infer_with_records(&value_expr, &records);
    assert!(!value_unifier.has_errors());
    assert_eq!(value_ty, Type::Int);
}

#[test]
fn infer_pattern_match_on_opaque_constructor() {
    let mut records = RecordRegistry::new();
    records
        .register_opaque(&make_opaque_def(
            "UserId",
            vec![],
            TypeAnnotation::Named("Int".to_string()),
            vec![],
        ))
        .expect("opaque registration");

    let expr = sp(ExprKind::Case {
        scrutinee: Box::new(constructor("UserId", vec![lit_int(7)])),
        arms: vec![arm(
            pat_constructor("UserId", vec![pat_var("n")]),
            binop(BinOp::Add, var("n"), lit_int(1)),
        )],
    });

    let (ty, unifier) = infer_with_records(&expr, &records);
    assert!(!unifier.has_errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn sum_type_self_recursive_registration_marks_recursive_fields() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let tree = make_type_def(
        "Tree",
        vec!["t"],
        vec![
            ("Leaf", vec![TypeAnnotation::Named("t".to_string())]),
            (
                "Branch",
                vec![
                    TypeAnnotation::Applied(
                        "Tree".to_string(),
                        vec![TypeAnnotation::Named("t".to_string())],
                    ),
                    TypeAnnotation::Applied(
                        "Tree".to_string(),
                        vec![TypeAnnotation::Named("t".to_string())],
                    ),
                ],
            ),
        ],
    );

    sums.register(&tree, &records)
        .expect("self-recursive sum type should register");

    let info = sums.lookup("Tree").expect("Tree should be registered");
    assert!(info.is_recursive, "Tree should be marked recursive");

    let leaf = info
        .variants
        .iter()
        .find(|variant| variant.name == "Leaf")
        .expect("Leaf variant exists");
    assert_eq!(leaf.recursive_fields, vec![false]);

    let branch = info
        .variants
        .iter()
        .find(|variant| variant.name == "Branch")
        .expect("Branch variant exists");
    assert_eq!(branch.recursive_fields, vec![true, true]);
}

#[test]
fn sum_type_mutual_recursion_registration_works() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let expr = make_type_def(
        "Expr",
        vec![],
        vec![
            ("Lit", vec![TypeAnnotation::Named("Int".to_string())]),
            ("BodyExpr", vec![TypeAnnotation::Named("Body".to_string())]),
        ],
    );
    let body = make_type_def(
        "Body",
        vec![],
        vec![
            ("ExprBody", vec![TypeAnnotation::Named("Expr".to_string())]),
            ("EmptyBody", vec![]),
        ],
    );

    sums.register_many(&[&expr, &body], &records)
        .expect("mutually-recursive sum types should register");

    assert!(sums.is_recursive_type("Expr"));
    assert!(sums.is_recursive_type("Body"));

    let expr_info = sums.lookup("Expr").expect("Expr should be registered");
    let body_expr = expr_info
        .variants
        .iter()
        .find(|variant| variant.name == "BodyExpr")
        .expect("BodyExpr variant exists");
    assert_eq!(body_expr.recursive_fields, vec![true]);
}

#[test]
fn sum_type_variant_where_clause_registers_constraints() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let tagged = TypeDef {
        annotations: vec![],
        public: false,
        name: sp("Tagged".to_string()),
        doc: None,
        params: vec!["T".to_string()],
        variants: vec![
            TypeVariant {
                annotations: vec![],
                name: sp("TagInt".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Int".to_string())),
                }],
            },
            TypeVariant {
                annotations: vec![],
                name: sp("Wrap".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
                where_clause: vec![],
            },
        ],
        derives: vec![],
    };

    sums.register(&tagged, &records)
        .expect("type with variant where clause should register");
    let (_owner, variant) = sums
        .lookup_variant("TagInt")
        .expect("TagInt variant should be registered");
    assert_eq!(variant.where_constraints.len(), 1);
    assert_eq!(variant.where_constraints[0].0, Type::Var(TypeVarId(0)));
    assert_eq!(variant.where_constraints[0].1, Type::Int);
}

#[test]
fn sum_type_variant_where_clause_unknown_param_errors() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let tagged = TypeDef {
        annotations: vec![],
        public: false,
        name: sp("Tagged".to_string()),
        doc: None,
        params: vec!["T".to_string()],
        variants: vec![TypeVariant {
            annotations: vec![],
            name: sp("TagInt".to_string()),
            fields: vec![],
            where_clause: vec![VariantWhereItem {
                type_var: sp("U".to_string()),
                ty: sp(TypeAnnotation::Named("Int".to_string())),
            }],
        }],
        derives: vec![],
    };

    let err = sums
        .register(&tagged, &records)
        .expect_err("unknown where-clause type var should be rejected");
    assert!(
        err.message.contains("unknown type parameter `U`"),
        "unexpected error: {}",
        err.message
    );
}

#[test]
fn sum_type_variant_where_clause_accepts_phantom_constraint_param() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let tagged = TypeDef {
        annotations: vec![],
        public: false,
        name: sp("Tagged".to_string()),
        doc: None,
        params: vec!["T".to_string()],
        variants: vec![TypeVariant {
            annotations: vec![],
            name: sp("TagInt".to_string()),
            fields: vec![],
            where_clause: vec![VariantWhereItem {
                type_var: sp("T".to_string()),
                ty: sp(TypeAnnotation::Named("Int".to_string())),
            }],
        }],
        derives: vec![],
    };

    sums.register(&tagged, &records)
        .expect("phantom where-clause parameter should register");
    let (_owner, variant) = sums
        .lookup_variant("TagInt")
        .expect("TagInt variant should be registered");
    assert_eq!(variant.where_constraints.len(), 1);
    assert_eq!(variant.where_constraints[0].0, Type::Var(TypeVarId(0)));
    assert_eq!(variant.where_constraints[0].1, Type::Int);
}

#[test]
fn constructor_enforces_variant_where_clause_constraints() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let constrained = TypeDef {
        annotations: vec![],
        public: false,
        name: sp("Constrained".to_string()),
        doc: None,
        params: vec!["T".to_string()],
        variants: vec![TypeVariant {
            annotations: vec![],
            name: sp("OnlyInt".to_string()),
            fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
            where_clause: vec![VariantWhereItem {
                type_var: sp("T".to_string()),
                ty: sp(TypeAnnotation::Named("Int".to_string())),
            }],
        }],
        derives: vec![],
    };
    sums.register(&constrained, &records)
        .expect("Constrained should register");

    let mut env = TypeEnv::new();
    let mut unifier = Unifier::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let expr = constructor("OnlyInt", vec![lit_bool(true)]);
    let _ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);

    assert!(
        unifier.has_errors(),
        "constructor should fail when where-clause equality is violated"
    );
}

#[test]
fn constructor_enforces_variant_where_clause_constraints_bool_variant() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let constrained = TypeDef {
        annotations: vec![],
        public: false,
        name: sp("Constrained".to_string()),
        doc: None,
        params: vec!["T".to_string()],
        variants: vec![
            TypeVariant {
                annotations: vec![],
                name: sp("OnlyInt".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Int".to_string())),
                }],
            },
            TypeVariant {
                annotations: vec![],
                name: sp("OnlyBool".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Bool".to_string())),
                }],
            },
        ],
        derives: vec![],
    };
    sums.register(&constrained, &records)
        .expect("Constrained should register");

    let mut env_ok = TypeEnv::new();
    let mut unifier_ok = Unifier::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let ok_expr = constructor("OnlyBool", vec![lit_bool(true)]);
    let _ok_ty = infer_and_resolve(
        &ok_expr,
        &mut env_ok,
        &mut unifier_ok,
        &records,
        &traits,
        &sums,
    );
    assert!(
        !unifier_ok.has_errors(),
        "bool constrained constructor with Bool payload should typecheck: {:?}",
        unifier_ok.errors()
    );

    let mut env_bad = TypeEnv::new();
    let mut unifier_bad = Unifier::new();
    let bad_expr = constructor("OnlyBool", vec![lit_int(1)]);
    let _bad_ty = infer_and_resolve(
        &bad_expr,
        &mut env_bad,
        &mut unifier_bad,
        &records,
        &traits,
        &sums,
    );
    assert!(
        unifier_bad.has_errors(),
        "bool constrained constructor should fail for Int payload"
    );
}

#[test]
fn case_arms_do_not_leak_variant_where_clause_constraints() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let tagged = TypeDef {
        annotations: vec![],
        public: false,
        name: sp("Tagged".to_string()),
        doc: None,
        params: vec!["T".to_string()],
        variants: vec![
            TypeVariant {
                annotations: vec![],
                name: sp("TagInt".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Int".to_string())),
                }],
            },
            TypeVariant {
                annotations: vec![],
                name: sp("TagBool".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Bool".to_string())),
                }],
            },
        ],
        derives: vec![],
    };
    sums.register(&tagged, &records)
        .expect("Tagged should register");

    let mut env = TypeEnv::new();
    let mut unifier = Unifier::new();
    let tagged_ty = sums
        .to_type_with("Tagged", &mut Some(&mut unifier))
        .expect("Tagged should instantiate");
    env.bind("x".to_string(), TypeScheme::mono(tagged_ty));

    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let expr = sp(ExprKind::Case {
        scrutinee: Box::new(var("x")),
        arms: vec![
            arm(
                pat_constructor("TagInt", vec![pat_var("n")]),
                block(vec![var("n"), lit_int(1)]),
            ),
            arm(
                pat_constructor("TagBool", vec![pat_var("b")]),
                block(vec![var("b"), lit_int(0)]),
            ),
        ],
    });

    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        !unifier.has_errors(),
        "variant constraints should stay branch-local: {:?}",
        unifier.errors()
    );
    assert_eq!(unifier.substitution.apply(&ty), Type::Int);
}

#[test]
fn case_exhaustiveness_ignores_unreachable_gadt_variants() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let tagged = TypeDef {
        annotations: vec![],
        public: false,
        name: sp("Tagged".to_string()),
        doc: None,
        params: vec!["T".to_string()],
        variants: vec![
            TypeVariant {
                annotations: vec![],
                name: sp("TagInt".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Int".to_string())),
                }],
            },
            TypeVariant {
                annotations: vec![],
                name: sp("TagBool".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Bool".to_string())),
                }],
            },
        ],
        derives: vec![],
    };
    sums.register(&tagged, &records)
        .expect("Tagged should register");

    let mut env = TypeEnv::new();
    let mut unifier = Unifier::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let expr = sp(ExprKind::Case {
        scrutinee: Box::new(constructor("TagInt", vec![lit_int(1)])),
        arms: vec![arm(
            pat_constructor("TagInt", vec![pat_var("n")]),
            block(vec![var("n"), lit_int(1)]),
        )],
    });

    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        !unifier.has_errors(),
        "unreachable constrained variants should not be required for exhaustiveness: {:?}",
        unifier.errors()
    );
    assert_eq!(unifier.substitution.apply(&ty), Type::Int);
}

#[test]
fn case_exhaustiveness_ignores_unreachable_phantom_gadt_variants() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let expr_ty = TypeDef {
        annotations: vec![],
        public: false,
        name: sp("Expr".to_string()),
        doc: None,
        params: vec!["T".to_string()],
        variants: vec![
            TypeVariant {
                annotations: vec![],
                name: sp("LitInt".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("Int".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Int".to_string())),
                }],
            },
            TypeVariant {
                annotations: vec![],
                name: sp("IsZero".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("Int".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Bool".to_string())),
                }],
            },
        ],
        derives: vec![],
    };
    sums.register(&expr_ty, &records)
        .expect("Expr should register");

    let mut env = TypeEnv::new();
    let mut unifier = Unifier::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let expr = sp(ExprKind::Case {
        scrutinee: Box::new(constructor("LitInt", vec![lit_int(1)])),
        arms: vec![arm(
            pat_constructor("LitInt", vec![pat_var("n")]),
            block(vec![var("n"), lit_int(1)]),
        )],
    });

    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        !unifier.has_errors(),
        "unreachable phantom-constrained variants should not be required for exhaustiveness: {:?}",
        unifier.errors()
    );
    assert_eq!(unifier.substitution.apply(&ty), Type::Int);
}

#[test]
fn case_ignores_unreachable_gadt_arms_without_errors() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let tagged = TypeDef {
        annotations: vec![],
        public: false,
        name: sp("Tagged".to_string()),
        doc: None,
        params: vec!["T".to_string()],
        variants: vec![
            TypeVariant {
                annotations: vec![],
                name: sp("TagInt".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Int".to_string())),
                }],
            },
            TypeVariant {
                annotations: vec![],
                name: sp("TagBool".to_string()),
                fields: vec![variant_field(TypeAnnotation::Named("T".to_string()))],
                where_clause: vec![VariantWhereItem {
                    type_var: sp("T".to_string()),
                    ty: sp(TypeAnnotation::Named("Bool".to_string())),
                }],
            },
        ],
        derives: vec![],
    };
    sums.register(&tagged, &records)
        .expect("Tagged should register");

    let mut env = TypeEnv::new();
    let mut unifier = Unifier::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let expr = sp(ExprKind::Case {
        scrutinee: Box::new(constructor("TagInt", vec![lit_int(1)])),
        arms: vec![
            arm(
                pat_constructor("TagInt", vec![pat_var("n")]),
                block(vec![var("n"), lit_int(1)]),
            ),
            arm(
                pat_constructor("TagBool", vec![pat_var("b")]),
                block(vec![var("b"), lit_int(0)]),
            ),
        ],
    });

    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        !unifier.has_errors(),
        "unreachable constrained case arm should not error: {:?}",
        unifier.errors()
    );
    assert!(
        unifier.errors().iter().any(|diag| {
            matches!(diag.severity, kea_diag::Severity::Warning)
                && diag
                    .message
                    .contains("unreachable constructor arm `TagBool`")
        }),
        "expected unreachable-arm warning, got: {:?}",
        unifier.errors()
    );
    assert_eq!(unifier.substitution.apply(&ty), Type::Int);
}

#[test]
fn await_inside_actor_context_emits_deadlock_warning() {
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let mut env = TypeEnv::new();
    env.push_actor_context();
    env.bind(
        "t".into(),
        TypeScheme::mono(Type::Task(Box::new(Type::Int))),
    );
    let expr = sp(ExprKind::Await {
        expr: Box::new(var("t")),
        safe: false,
    });

    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    env.pop_actor_context();

    assert_eq!(unifier.substitution.apply(&ty), Type::Int);
    assert!(
        unifier.errors().iter().any(|diag| {
            matches!(diag.severity, kea_diag::Severity::Warning)
                && diag.code.as_deref() == Some("W0901")
                && diag
                    .message
                    .contains("await inside actor handler may cause deadlock")
        }),
        "expected W0901 warning, got: {:?}",
        unifier.errors()
    );
}

// ===========================================================================
// Literal inference
// ===========================================================================

#[test]
fn infer_int_literal() {
    let (ty, u) = infer(&lit_int(42));
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_float_literal() {
    let (ty, u) = infer(&lit_float(1.5));
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Float);
}

#[test]
fn infer_bool_literal() {
    let (ty, u) = infer(&lit_bool(true));
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_string_literal() {
    let (ty, u) = infer(&lit_str("hello"));
    assert!(!u.has_errors());
    assert_eq!(ty, Type::String);
}

#[test]
fn infer_unit_literal() {
    let (ty, u) = infer(&lit_unit());
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Unit);
}

// ===========================================================================
// Variable lookup
// ===========================================================================

#[test]
fn infer_undefined_variable() {
    let (_, u) = infer(&var("x"));
    assert!(u.has_errors());
    assert!(u.errors()[0].message.contains("undefined variable"));
}

#[test]
fn infer_bound_variable() {
    let mut env = TypeEnv::new();
    env.bind("x".into(), TypeScheme::mono(Type::Int));
    let (ty, u) = infer_with_env(&var("x"), &mut env);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Int);
}

// ===========================================================================
// Let bindings
// ===========================================================================

#[test]
fn infer_let_simple() {
    // { let x = 42; x }  →  Int
    let expr = block(vec![let_bind("x", lit_int(42)), var("x")]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_let_shadowing() {
    // { let x = 42; let x = "hello"; x }  →  String
    let expr = block(vec![
        let_bind("x", lit_int(42)),
        let_bind("x", lit_str("hello")),
        var("x"),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::String);
}

// ===========================================================================
// Lambda and application
// ===========================================================================

#[test]
fn infer_lambda_identity() {
    // |x| x  →  a -> a (for some var a)
    let expr = lambda(&["x"], var("x"));
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    match &ty {
        Type::Function(ft) => {
            assert_eq!(ft.params.len(), 1);
            assert_eq!(ft.params[0], ft.ret.as_ref().clone());
        }
        _ => panic!("Expected function type, got {ty:?}"),
    }
}

#[test]
fn infer_lambda_application() {
    // (|x| x)(42)  →  Int
    let expr = call(lambda(&["x"], var("x")), vec![lit_int(42)]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_lambda_const() {
    // (|x, y| x)(42, "hello")  →  Int
    let expr = call(
        lambda(&["x", "y"], var("x")),
        vec![lit_int(42), lit_str("hello")],
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_application_wrong_arity() {
    // (|x| x)(1, 2)  →  error
    let expr = call(lambda(&["x"], var("x")), vec![lit_int(1), lit_int(2)]);
    let (_, u) = infer(&expr);
    assert!(u.has_errors());
}

// ===========================================================================
// Let-generalization (polymorphism)
// ===========================================================================

#[test]
fn infer_let_polymorphic_identity() {
    // { let id = |x| x; #(id(42), id("hello")) }  →  #(Int, String)
    //
    // This is the classic HM test: `id` must be used at two different types
    // in the same expression. Without let-generalization, this would fail.
    let expr = block(vec![
        let_bind("id", lambda(&["x"], var("x"))),
        tuple(vec![
            call(var("id"), vec![lit_int(42)]),
            call(var("id"), vec![lit_str("hello")]),
        ]),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Tuple(vec![Type::Int, Type::String]));
}

#[test]
fn infer_let_polymorphic_const() {
    // { let const_ = |x, y| x; #(const_(42, true), const_("a", "b")) }
    //   →  #(Int, String)
    let expr = block(vec![
        let_bind("const_", lambda(&["x", "y"], var("x"))),
        tuple(vec![
            call(var("const_"), vec![lit_int(42), lit_bool(true)]),
            call(var("const_"), vec![lit_str("a"), lit_str("b")]),
        ]),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Tuple(vec![Type::Int, Type::String]));
}

#[test]
fn infer_let_monomorphic_lambda_arg() {
    // Lambda args are NOT generalized — they're monomorphic.
    // |f| #(f(42), f("hello"))  →  error (f can't be both Int->? and String->?)
    let expr = lambda(
        &["f"],
        tuple(vec![
            call(var("f"), vec![lit_int(42)]),
            call(var("f"), vec![lit_str("hello")]),
        ]),
    );
    let (_, u) = infer(&expr);
    assert!(u.has_errors(), "Lambda args should not be generalized");
}

#[test]
fn infer_nested_let_generalization() {
    // { let id = |x| x; let apply_id = |y| id(y); apply_id(42) }  →  Int
    let expr = block(vec![
        let_bind("id", lambda(&["x"], var("x"))),
        let_bind("apply_id", lambda(&["y"], call(var("id"), vec![var("y")]))),
        call(var("apply_id"), vec![lit_int(42)]),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_nested_stream_call_resolves_inner_type_parameter() {
    let mut env = TypeEnv::new();
    let a = TypeVarId(1000);
    let b = TypeVarId(1001);
    let c = TypeVarId(1002);

    env.bind(
        "stream_from_task".to_string(),
        TypeScheme {
            type_vars: vec![a],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: Default::default(),
            ty: Type::Function(FunctionType {
                params: vec![Type::List(Box::new(Type::Var(a)))],
                ret: Box::new(Type::Stream(Box::new(Type::Var(a)))),
                effects: EffectRow::pure(),
            }),
        },
    );

    env.bind(
        "stream_map".to_string(),
        TypeScheme {
            type_vars: vec![b, c],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: Default::default(),
            ty: Type::Function(FunctionType {
                params: vec![
                    Type::Stream(Box::new(Type::Var(b))),
                    Type::Function(FunctionType {
                        params: vec![Type::Var(b)],
                        ret: Box::new(Type::Var(c)),
                        effects: EffectRow::pure(),
                    }),
                ],
                ret: Box::new(Type::Stream(Box::new(Type::Var(c)))),
                effects: EffectRow::pure(),
            }),
        },
    );

    let expr = call(
        var("stream_map"),
        vec![
            call(
                var("stream_from_task"),
                vec![list(vec![lit_int(1), lit_int(2), lit_int(3)])],
            ),
            lambda(&["x"], binop(BinOp::Mul, var("x"), lit_int(2))),
        ],
    );

    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Stream(Box::new(Type::Int)));
}

#[test]
fn infer_stream_block_with_yields_has_stream_type() {
    let expr = stream_block(block(vec![
        yield_expr(lit_int(1)),
        yield_expr(lit_int(2)),
        yield_expr(lit_int(3)),
    ]));
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Stream(Box::new(Type::Int)));
}

#[test]
fn infer_yield_outside_stream_errors() {
    let expr = yield_expr(lit_int(42));
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "yield outside stream should error");
}

#[test]
fn infer_stream_block_rejects_mixed_yield_types() {
    let expr = stream_block(block(vec![
        yield_expr(lit_int(1)),
        yield_expr(lit_str("x")),
    ]));
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "mixed yield types should error");
}

#[test]
fn infer_stream_block_rejects_yield_from_mismatch() {
    let expr = stream_block(block(vec![
        yield_expr(lit_int(1)),
        yield_from_expr(stream_block(yield_expr(lit_str("x")))),
    ]));
    let (_ty, u) = infer(&expr);
    assert!(
        u.has_errors(),
        "yield_from element type mismatch should error"
    );
}

#[test]
fn infer_for_list_with_guard_returns_list() {
    let expr = for_expr(
        vec![
            for_gen(
                sp(PatternKind::Var("x".to_string())),
                list(vec![lit_int(1), lit_int(2)]),
            ),
            for_guard(binop(BinOp::Gt, var("x"), lit_int(1))),
        ],
        binop(BinOp::Mul, var("x"), lit_int(2)),
    );

    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_for_records_bind_trait_desugaring() {
    let expr = for_expr(
        vec![for_gen(
            sp(PatternKind::Var("x".to_string())),
            list(vec![lit_int(1), lit_int(2)]),
        )],
        binop(BinOp::Add, var("x"), lit_int(1)),
    );

    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));

    let lowered = u
        .type_annotations
        .for_desugared
        .get(&expr.span)
        .expect("expected lowered for annotation");
    let ExprKind::Call { func, .. } = &lowered.node else {
        panic!(
            "expected lowered for root to be a call, got {:?}",
            lowered.node
        );
    };
    let ExprKind::FieldAccess { expr, field } = &func.node else {
        panic!(
            "expected lowered for root call to target trait method, got {:?}",
            func.node
        );
    };
    assert_eq!(field.node, "map");
    let ExprKind::Var(name) = &expr.node else {
        panic!(
            "expected trait receiver to be variable, got {:?}",
            expr.node
        );
    };
    assert_eq!(name, "Comprehensible");
}

#[test]
fn infer_for_simple_guard_desugars_to_comprehensible_filter_then_map() {
    let expr = for_expr(
        vec![
            for_gen(
                sp(PatternKind::Var("x".to_string())),
                list(vec![lit_int(1), lit_int(2), lit_int(3)]),
            ),
            for_guard(binop(BinOp::Gt, var("x"), lit_int(1))),
        ],
        binop(BinOp::Mul, var("x"), lit_int(2)),
    );

    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));

    let lowered = u
        .type_annotations
        .for_desugared
        .get(&expr.span)
        .expect("expected lowered for annotation");
    let ExprKind::Call { func, args } = &lowered.node else {
        panic!(
            "expected lowered for root to be a call, got {:?}",
            lowered.node
        );
    };
    let ExprKind::FieldAccess { expr, field } = &func.node else {
        panic!(
            "expected lowered for root call to target trait method, got {:?}",
            func.node
        );
    };
    assert_eq!(field.node, "map");
    let ExprKind::Var(name) = &expr.node else {
        panic!(
            "expected trait receiver to be variable, got {:?}",
            expr.node
        );
    };
    assert_eq!(name, "Comprehensible");

    let source_arg = args.first().expect("map should have source argument");
    let ExprKind::Call { func, .. } = &source_arg.value.node else {
        panic!(
            "expected map source arg to be a filter call, got {:?}",
            source_arg.value.node
        );
    };
    let ExprKind::FieldAccess { expr, field } = &func.node else {
        panic!(
            "expected filter call target to be trait method, got {:?}",
            func.node
        );
    };
    assert_eq!(field.node, "filter");
    let ExprKind::Var(name) = &expr.node else {
        panic!(
            "expected filter trait receiver to be variable, got {:?}",
            expr.node
        );
    };
    assert_eq!(name, "Comprehensible");
}

#[test]
fn infer_for_independent_two_generators_desugars_to_applicative_apply() {
    let expr = for_expr(
        vec![
            for_gen(
                sp(PatternKind::Var("x".to_string())),
                list(vec![lit_int(1), lit_int(2)]),
            ),
            for_gen(
                sp(PatternKind::Var("y".to_string())),
                list(vec![lit_int(10), lit_int(20)]),
            ),
        ],
        binop(BinOp::Add, var("x"), var("y")),
    );

    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));

    let lowered = u
        .type_annotations
        .for_desugared
        .get(&expr.span)
        .expect("expected lowered for annotation");
    let ExprKind::Call { func, .. } = &lowered.node else {
        panic!(
            "expected lowered for root to be a call, got {:?}",
            lowered.node
        );
    };
    let ExprKind::FieldAccess { expr, field } = &func.node else {
        panic!(
            "expected lowered for root call to target trait method, got {:?}",
            func.node
        );
    };
    assert_eq!(field.node, "apply");
    let ExprKind::Var(name) = &expr.node else {
        panic!(
            "expected trait receiver to be variable, got {:?}",
            expr.node
        );
    };
    assert_eq!(name, "Applicative");
}

#[test]
fn infer_for_dependent_two_generators_desugars_to_bind() {
    let expr = for_expr(
        vec![
            for_gen(
                sp(PatternKind::Var("x".to_string())),
                list(vec![lit_int(1), lit_int(2)]),
            ),
            for_gen(
                sp(PatternKind::Var("y".to_string())),
                list(vec![var("x"), binop(BinOp::Add, var("x"), lit_int(1))]),
            ),
        ],
        binop(BinOp::Add, var("x"), var("y")),
    );

    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));

    let lowered = u
        .type_annotations
        .for_desugared
        .get(&expr.span)
        .expect("expected lowered for annotation");
    let ExprKind::Call { func, .. } = &lowered.node else {
        panic!(
            "expected lowered for root to be a call, got {:?}",
            lowered.node
        );
    };
    let ExprKind::FieldAccess { expr, field } = &func.node else {
        panic!(
            "expected lowered for root call to target trait method, got {:?}",
            func.node
        );
    };
    assert_eq!(field.node, "bind");
    let ExprKind::Var(name) = &expr.node else {
        panic!(
            "expected trait receiver to be variable, got {:?}",
            expr.node
        );
    };
    assert_eq!(name, "Bind");
}

#[test]
fn infer_for_option_returns_option() {
    let expr = for_expr(
        vec![for_gen(
            sp(PatternKind::Var("x".to_string())),
            constructor("Some", vec![lit_int(1)]),
        )],
        binop(BinOp::Add, var("x"), lit_int(1)),
    );

    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Option(Box::new(Type::Int)));
}

#[test]
fn infer_for_result_returns_result() {
    let expr = for_expr(
        vec![
            for_gen(
                sp(PatternKind::Var("x".to_string())),
                constructor("Ok", vec![lit_int(1)]),
            ),
            for_gen(
                sp(PatternKind::Var("y".to_string())),
                constructor("Ok", vec![lit_int(2)]),
            ),
        ],
        binop(BinOp::Add, var("x"), var("y")),
    );

    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    match ty {
        Type::Result(ok, _err) => assert_eq!(*ok, Type::Int),
        other => panic!("expected Result(Int, e), got {other:?}"),
    }
}

#[test]
fn infer_for_pattern_generator_filters_item_type() {
    let expr = for_expr(
        vec![for_gen(
            constructor_pattern("Ok", vec![sp(PatternKind::Var("x".to_string()))]),
            list(vec![
                constructor("Ok", vec![lit_int(1)]),
                constructor("Err", vec![lit_str("bad")]),
            ]),
        )],
        var("x"),
    );

    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_for_guard_requires_bool() {
    let expr = for_expr(
        vec![
            for_gen(
                sp(PatternKind::Var("x".to_string())),
                list(vec![lit_int(1), lit_int(2)]),
            ),
            for_guard(lit_int(1)),
        ],
        var("x"),
    );

    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "non-bool guard should error");
    assert_eq!(
        u.errors()[0].message,
        "guard expression must be Bool, got `Int`"
    );
}

#[test]
fn infer_for_into_set_returns_set() {
    let expr = for_expr_into(
        vec![for_gen(
            sp(PatternKind::Var("x".to_string())),
            list(vec![lit_int(1), lit_int(2), lit_int(2)]),
        )],
        var("x"),
        "Set",
    );

    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Set(Box::new(Type::Int)));
}

#[test]
fn infer_for_into_map_requires_tuple_body() {
    let expr = for_expr_into(
        vec![for_gen(
            sp(PatternKind::Var("x".to_string())),
            list(vec![lit_int(1), lit_int(2)]),
        )],
        var("x"),
        "Map",
    );

    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "into Map without tuple body should error");
    assert_eq!(
        u.errors()[0].message,
        "cannot collect into Map — body must yield 2-tuples, got `Int`"
    );
    let help = u.errors()[0].help.as_deref().unwrap_or_default();
    assert!(
        help.contains("(key, value)"),
        "expected tuple suggestion in help, got: {help}"
    );
}

#[test]
fn infer_for_over_non_comprehensible_type_reports_error() {
    let expr = for_expr(
        vec![for_gen(sp(PatternKind::Var("x".to_string())), lit_int(1))],
        var("x"),
    );

    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "for over plain Int should error");
    assert_eq!(u.errors()[0].message, "cannot iterate over `Int`");
    let help = u.errors()[0].help.as_deref().unwrap_or_default();
    assert!(
        help.contains("this type does not implement Comprehensible"),
        "expected Comprehensible help detail, got: {help}"
    );
    assert!(
        help.contains("no `Comprehensible` impl found for type constructor `Int`"),
        "expected solver mismatch detail in help, got: {help}"
    );
}

#[test]
fn infer_for_non_list_like_tuple_pattern_typechecks() {
    let expr = for_expr(
        vec![for_gen(
            sp(PatternKind::Tuple(vec![
                sp(PatternKind::Var("x".to_string())),
                sp(PatternKind::Var("y".to_string())),
            ])),
            constructor("Some", vec![tuple(vec![lit_int(1), lit_int(2)])]),
        )],
        sp(ExprKind::BinaryOp {
            op: sp(BinOp::Add),
            left: Box::new(var("x")),
            right: Box::new(var("y")),
        }),
    );

    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    let resolved = u.substitution.apply(&ty);
    match resolved {
        Type::Option(ok) => assert_eq!(*ok, Type::Int),
        other => panic!("expected Option(Int), got {other:?}"),
    }
}

#[test]
fn infer_nested_list_call_resolves_inner_type_parameter() {
    let mut env = TypeEnv::new();
    let a = TypeVarId(1010);
    let b = TypeVarId(1011);
    let c = TypeVarId(1012);

    env.bind(
        "list_sort".to_string(),
        TypeScheme {
            type_vars: vec![a],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: Default::default(),
            ty: Type::Function(FunctionType {
                params: vec![Type::List(Box::new(Type::Var(a)))],
                ret: Box::new(Type::List(Box::new(Type::Var(a)))),
                effects: EffectRow::pure(),
            }),
        },
    );

    env.bind(
        "list_map".to_string(),
        TypeScheme {
            type_vars: vec![b, c],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: Default::default(),
            ty: Type::Function(FunctionType {
                params: vec![
                    Type::List(Box::new(Type::Var(b))),
                    Type::Function(FunctionType {
                        params: vec![Type::Var(b)],
                        ret: Box::new(Type::Var(c)),
                        effects: EffectRow::pure(),
                    }),
                ],
                ret: Box::new(Type::List(Box::new(Type::Var(c)))),
                effects: EffectRow::pure(),
            }),
        },
    );

    let expr = call(
        var("list_map"),
        vec![
            call(
                var("list_sort"),
                vec![list(vec![lit_int(3), lit_int(1), lit_int(2)])],
            ),
            lambda(&["x"], binop(BinOp::Mul, var("x"), lit_int(2))),
        ],
    );

    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

// ===========================================================================
// If expressions
// ===========================================================================

#[test]
fn infer_if_expression() {
    // if true { 42 } else { 0 }  →  Int
    let expr = if_expr(lit_bool(true), lit_int(42), Some(lit_int(0)));
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_if_branch_mismatch() {
    // if true { 42 } else { "hello" }  →  error
    let expr = if_expr(lit_bool(true), lit_int(42), Some(lit_str("hello")));
    let (_, u) = infer(&expr);
    assert!(u.has_errors());
}

#[test]
fn infer_if_condition_not_bool() {
    // if 42 { true } else { false }  →  error
    let expr = if_expr(lit_int(42), lit_bool(true), Some(lit_bool(false)));
    let (_, u) = infer(&expr);
    assert!(u.has_errors());
}

#[test]
fn infer_if_no_else() {
    // `if` without `else` is now a parser error; if an invalid AST reaches typeck,
    // report an internal type error instead of treating it as Unit.
    let expr = if_expr(lit_bool(true), lit_unit(), None);
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors());
    assert!(
        u.errors
            .iter()
            .any(|d| d.message.contains("`if` without `else`")),
        "expected missing-else internal error, got {:?}",
        u.errors
    );
}

#[test]
fn infer_if_option_is_some_narrows_true_branch() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    let expr = if_expr(
        call(field_access(var("Option"), "is_some"), vec![var("x")]),
        binop(BinOp::Add, var("x"), lit_int(1)),
        Some(lit_int(0)),
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "is_some guard should narrow true branch: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_if_option_is_none_narrows_else_branch() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    let expr = if_expr(
        call(field_access(var("Option"), "is_none"), vec![var("x")]),
        lit_int(0),
        Some(binop(BinOp::Add, var("x"), lit_int(1))),
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "is_none guard should narrow else branch: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_if_not_option_is_none_narrows_true_branch() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    let expr = if_expr(
        unary(
            UnaryOp::Not,
            call(field_access(var("Option"), "is_none"), vec![var("x")]),
        ),
        binop(BinOp::Add, var("x"), lit_int(1)),
        Some(lit_int(0)),
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "not is_none guard should narrow true branch: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_if_not_option_is_some_narrows_else_branch() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    let expr = if_expr(
        unary(
            UnaryOp::Not,
            call(field_access(var("Option"), "is_some"), vec![var("x")]),
        ),
        lit_int(0),
        Some(binop(BinOp::Add, var("x"), lit_int(1))),
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "not is_some guard should narrow else branch: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_if_left_arg_application_guard_narrows_true_branch() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    let expr = if_expr(
        apply_first_arg(var("x"), field_access(var("Option"), "is_some")),
        binop(BinOp::Add, var("x"), lit_int(1)),
        Some(lit_int(0)),
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "left-arg application guard should narrow true branch: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_if_result_guard_narrows_both_branches() {
    let mut env = TypeEnv::new();
    env.bind(
        "r".into(),
        TypeScheme::mono(Type::Result(Box::new(Type::Int), Box::new(Type::String))),
    );
    let expr = if_expr(
        call(field_access(var("Result"), "is_ok"), vec![var("r")]),
        binop(BinOp::Eq, var("r"), lit_int(1)),
        Some(binop(BinOp::Eq, var("r"), lit_str("error"))),
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "result guard should narrow ok/err branches: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_if_and_short_circuit_sees_narrowed_rhs() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    let expr = if_expr(
        binop(
            BinOp::And,
            call(field_access(var("Option"), "is_some"), vec![var("x")]),
            binop(BinOp::Gt, var("x"), lit_int(0)),
        ),
        var("x"),
        Some(lit_int(0)),
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "rhs of && should type-check under narrowed x: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_if_or_short_circuit_sees_complement_narrowed_rhs() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    let expr = if_expr(
        binop(
            BinOp::Or,
            call(field_access(var("Option"), "is_none"), vec![var("x")]),
            binop(BinOp::Gt, var("x"), lit_int(0)),
        ),
        lit_int(1),
        Some(lit_int(0)),
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "rhs of || should type-check under complement narrowing: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_if_intermediate_bool_does_not_narrow() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    env.bind(
        "is_some".into(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Option(Box::new(Type::Int))],
            ret: Box::new(Type::Bool),
            effects: EffectRow::pure(),
        })),
    );
    let expr = block(vec![
        let_bind("ok", call(var("is_some"), vec![var("x")])),
        if_expr(
            var("ok"),
            binop(BinOp::Add, var("x"), lit_int(1)),
            Some(lit_int(0)),
        ),
    ]);
    let (_, u) = infer_with_env(&expr, &mut env);
    assert!(
        u.has_errors(),
        "indirect bool guard should not narrow x, expected type error"
    );
}

#[test]
fn infer_if_non_narrowing_bool_function_does_not_narrow() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    env.bind(
        "my_check".into(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Option(Box::new(Type::Int))],
            ret: Box::new(Type::Bool),
            effects: EffectRow::pure(),
        })),
    );

    let expr = if_expr(
        call(var("my_check"), vec![var("x")]),
        binop(BinOp::Add, var("x"), lit_int(1)),
        Some(lit_int(0)),
    );

    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let mut unifier = Unifier::new();
    let sums = SumTypeRegistry::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);

    assert!(
        unifier.has_errors(),
        "non-narrowing bool function should not refine x in if-then branch"
    );
}

#[test]
fn infer_if_narrowing_does_not_leak_after_expression() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    let expr = block(vec![
        if_expr(
            call(field_access(var("Option"), "is_some"), vec![var("x")]),
            binop(BinOp::Add, var("x"), lit_int(1)),
            Some(lit_int(0)),
        ),
        binop(BinOp::Add, var("x"), lit_int(1)),
    ]);
    let (_, u) = infer_with_env(&expr, &mut env);
    assert!(
        u.has_errors(),
        "narrowing should be branch-local and must not leak after the if expression"
    );
}

#[test]
fn infer_if_sum_variant_predicate_narrows_single_field_payloads() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    sums.register(
        &make_type_def(
            "Shape",
            vec![],
            vec![
                ("Circle", vec![TypeAnnotation::Named("Int".to_string())]),
                ("Rect", vec![TypeAnnotation::Named("String".to_string())]),
            ],
        ),
        &records,
    )
    .expect("shape sum type should register");

    let mut env = TypeEnv::new();
    env.bind(
        "s".into(),
        TypeScheme::mono(sums.to_type("Shape").expect("shape type should exist")),
    );

    let expr = if_expr(
        call(field_access(var("Shape"), "is_circle"), vec![var("s")]),
        binop(BinOp::Eq, var("s"), lit_int(1)),
        Some(binop(BinOp::Eq, var("s"), lit_str("rect"))),
    );

    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);

    assert!(
        !unifier.has_errors(),
        "sum variant predicate should narrow branch payloads: {:?}",
        unifier.errors()
    );
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_if_sum_variant_predicate_constrains_unknown_binding() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    sums.register(
        &make_type_def(
            "Shape",
            vec![],
            vec![
                ("Circle", vec![TypeAnnotation::Named("Int".to_string())]),
                ("Rect", vec![TypeAnnotation::Named("String".to_string())]),
            ],
        ),
        &records,
    )
    .expect("shape sum type should register");

    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let mut unifier = Unifier::new();

    let unknown = unifier.fresh_type();
    env.bind("s".into(), TypeScheme::mono(unknown.clone()));

    let expr = if_expr(
        call(field_access(var("Shape"), "is_circle"), vec![var("s")]),
        binop(BinOp::Eq, var("s"), lit_int(1)),
        Some(binop(BinOp::Eq, var("s"), lit_str("rect"))),
    );

    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    let resolved_unknown = unifier.substitution.apply(&unknown);

    assert!(
        !unifier.has_errors(),
        "sum guard should constrain unknown binding and narrow branches: {:?}",
        unifier.errors()
    );
    assert_eq!(ty, Type::Bool);
    assert!(
        matches!(resolved_unknown, Type::Sum(ref sum) if sum.name == "Shape"),
        "expected guard to constrain binding to Shape, got {resolved_unknown:?}"
    );
}

#[test]
fn infer_if_left_arg_application_sum_variant_guard_narrows_branch() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    sums.register(
        &make_type_def(
            "Shape",
            vec![],
            vec![
                ("Circle", vec![TypeAnnotation::Named("Int".to_string())]),
                ("Rect", vec![TypeAnnotation::Named("String".to_string())]),
            ],
        ),
        &records,
    )
    .expect("shape sum type should register");

    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let mut unifier = Unifier::new();

    let unknown = unifier.fresh_type();
    env.bind("s".into(), TypeScheme::mono(unknown));

    let expr = if_expr(
        apply_first_arg(var("s"), field_access(var("Shape"), "is_circle")),
        binop(BinOp::Eq, var("s"), lit_int(1)),
        Some(binop(BinOp::Eq, var("s"), lit_str("rect"))),
    );

    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);

    assert!(
        !unifier.has_errors(),
        "left-arg application sum guard should narrow branches: {:?}",
        unifier.errors()
    );
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_if_parametric_sum_variant_guard_constrains_unknown_binding() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    sums.register(
        &make_type_def(
            "Either",
            vec!["L", "R"],
            vec![
                ("Left", vec![TypeAnnotation::Named("L".to_string())]),
                ("Right", vec![TypeAnnotation::Named("R".to_string())]),
            ],
        ),
        &records,
    )
    .expect("either sum type should register");

    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let mut unifier = Unifier::new();

    let unknown = unifier.fresh_type();
    env.bind("v".into(), TypeScheme::mono(unknown.clone()));

    let expr = if_expr(
        call(field_access(var("Either"), "is_left"), vec![var("v")]),
        binop(BinOp::Eq, var("v"), lit_int(7)),
        Some(binop(BinOp::Eq, var("v"), lit_str("err"))),
    );

    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    let resolved_unknown = unifier.substitution.apply(&unknown);

    assert!(
        !unifier.has_errors(),
        "parametric sum guard should constrain unknown binding and narrow branches: {:?}",
        unifier.errors()
    );
    assert_eq!(ty, Type::Bool);
    assert!(
        matches!(resolved_unknown, Type::Sum(ref sum) if sum.name == "Either"),
        "expected guard to constrain binding to Either, got {resolved_unknown:?}"
    );
}

#[test]
fn infer_cond_guard_narrows_arm_body() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    let expr = cond_expr(vec![
        cond_arm(
            call(field_access(var("Option"), "is_some"), vec![var("x")]),
            binop(BinOp::Add, var("x"), lit_int(1)),
        ),
        cond_wildcard_arm(lit_int(0)),
    ]);
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "cond arm should type-check under guard narrowing: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::Int);
}

// ===========================================================================
// Binary operators
// ===========================================================================

#[test]
fn infer_arithmetic() {
    // 1 + 2  →  Int
    let expr = binop(BinOp::Add, lit_int(1), lit_int(2));
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_concat_strings() {
    let expr = binop(BinOp::Concat, lit_str("hello "), lit_str("world"));
    let (ty, u) = infer(&expr);
    assert!(
        !u.has_errors(),
        "string concat should type-check: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::String);
}

#[test]
fn infer_concat_string_argument_to_typed_call() {
    let mut env = TypeEnv::new();
    let stdout_ty = Type::Function(FunctionType {
        params: vec![Type::String],
        effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
        ret: Box::new(Type::Unit),
    });
    env.bind("IO.stdout".into(), TypeScheme::mono(stdout_ty));
    let expr = call(
        var("IO.stdout"),
        vec![binop(BinOp::Concat, lit_str("hello "), lit_str("world"))],
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "string concat should satisfy typed call argument checking: {:?}",
        u.errors()
    );
    assert_eq!(ty, Type::Unit);
}

#[test]
fn infer_arithmetic_type_mismatch() {
    // 1 + "hello"  →  error
    let expr = binop(BinOp::Add, lit_int(1), lit_str("hello"));
    let (_, u) = infer(&expr);
    assert!(u.has_errors());
}

#[test]
fn infer_decimal_arithmetic_addition_computes_sql_dimensions() {
    let expr = binop(BinOp::Add, var("price"), var("fee"));
    let mut env = TypeEnv::new();
    env.bind("price".into(), TypeScheme::mono(decimal(10, 2)));
    env.bind("fee".into(), TypeScheme::mono(decimal(12, 4)));

    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "decimal addition should type-check, got: {:?}",
        u.errors()
    );
    assert_eq!(ty, decimal(13, 4));
}

#[test]
fn infer_decimal_arithmetic_division_computes_sql_dimensions() {
    let expr = binop(BinOp::Div, var("revenue"), var("ratio"));
    let mut env = TypeEnv::new();
    env.bind("revenue".into(), TypeScheme::mono(decimal(18, 2)));
    env.bind("ratio".into(), TypeScheme::mono(decimal(8, 4)));

    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "decimal division should type-check, got: {:?}",
        u.errors()
    );
    // precision = p1 + s2 + max(6, s1) = 18 + 4 + 6 = 28
    // scale = max(6, s1) = 6
    assert_eq!(ty, decimal(28, 6));
}

#[test]
fn infer_decimal_arithmetic_rejects_mixed_decimal_and_int() {
    let expr = binop(BinOp::Add, var("price"), var("count"));
    let mut env = TypeEnv::new();
    env.bind("price".into(), TypeScheme::mono(decimal(10, 2)));
    env.bind("count".into(), TypeScheme::mono(Type::Int));

    let (_ty, u) = infer_with_env(&expr, &mut env);
    assert!(u.has_errors(), "mixed decimal/int arithmetic should error");
}

#[test]
fn infer_comparison() {
    // 1 < 2  →  Bool
    let expr = binop(BinOp::Lt, lit_int(1), lit_int(2));
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_logical() {
    // true and false  →  Bool
    let expr = binop(BinOp::And, lit_bool(true), lit_bool(false));
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_logical_non_bool() {
    // 1 and 2  →  error
    let expr = binop(BinOp::And, lit_int(1), lit_int(2));
    let (_, u) = infer(&expr);
    assert!(u.has_errors());
}

#[test]
fn infer_range_type() {
    let expr = range_expr(lit_int(1), lit_int(10), false);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "range should type-check: {:?}", u.errors());
    assert_eq!(
        ty,
        Type::Opaque {
            name: "Range".to_string(),
            params: vec![Type::Int],
        }
    );
}

#[test]
fn infer_range_bounds_must_match() {
    let expr = range_expr(lit_int(1), lit_float(2.0), true);
    let (_, u) = infer(&expr);
    assert!(u.has_errors(), "mixed range bounds should fail");
    assert!(
        u.errors()
            .iter()
            .any(|d| d.message.contains("range bounds must have the same type")),
        "expected range bounds diagnostic, got: {:?}",
        u.errors()
    );
}

#[test]
fn infer_in_with_range() {
    let expr = binop(
        BinOp::In,
        lit_int(5),
        range_expr(lit_int(1), lit_int(10), false),
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "`in` with range should type-check");
    assert_eq!(ty, Type::Bool);
}

// ===========================================================================
// Tuples and lists
// ===========================================================================

#[test]
fn infer_tuple() {
    // #(42, "hello", true)  →  #(Int, String, Bool)
    let expr = tuple(vec![lit_int(42), lit_str("hello"), lit_bool(true)]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Tuple(vec![Type::Int, Type::String, Type::Bool]));
}

#[test]
fn infer_homogeneous_list() {
    // [1, 2, 3]  →  List(Int)
    let expr = list(vec![lit_int(1), lit_int(2), lit_int(3)]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_heterogeneous_list_error() {
    // [1, "hello"]  →  error
    let expr = list(vec![lit_int(1), lit_str("hello")]);
    let (_, u) = infer(&expr);
    assert!(u.has_errors());
}

// ===========================================================================
// Anonymous records and field access
// ===========================================================================

#[test]
fn infer_anon_record() {
    // #{ name: "alice", age: 30 }  →  #{ age: Int, name: String }
    let expr = anon_record(vec![("name", lit_str("alice")), ("age", lit_int(30))]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    match &ty {
        Type::AnonRecord(row) => {
            assert!(row.is_closed());
            assert_eq!(row.get(&Label::new("name")), Some(&Type::String));
            assert_eq!(row.get(&Label::new("age")), Some(&Type::Int));
        }
        _ => panic!("Expected AnonRecord, got {ty:?}"),
    }
}

#[test]
fn infer_anon_record_duplicate_field_errors() {
    let expr = anon_record(vec![("x", lit_int(1)), ("x", lit_int(2))]);
    let (_ty, u) = infer(&expr);
    assert!(
        u.has_errors(),
        "expected duplicate field diagnostic for anonymous record"
    );
    assert!(
        u.errors()
            .iter()
            .any(|d| d.message.contains("duplicate field `x`")),
        "expected duplicate field message, got {:?}",
        u.errors()
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );
}

#[test]
fn infer_anon_record_spread_redefined_field_errors() {
    let expr = sp(ExprKind::AnonRecord {
        fields: vec![(sp("x".to_string()), lit_int(10))],
        spread: Some(Box::new(anon_record(vec![("x", lit_int(1))]))),
    });
    let (_ty, u) = infer(&expr);
    assert!(
        u.has_errors(),
        "spread should reject labels already provided explicitly"
    );
}

#[test]
fn infer_field_access() {
    // (#{ name: "alice", age: 30 }).name  →  String
    let expr = field_access(
        anon_record(vec![("name", lit_str("alice")), ("age", lit_int(30))]),
        "name",
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::String);
}

#[test]
fn infer_field_access_missing() {
    // (#{ name: "alice" }).age  →  The unifier should still succeed (open row)
    // but the field type will be a fresh variable since the record has no `age`.
    // Actually, the record is closed, so this should fail.
    let expr = field_access(anon_record(vec![("name", lit_str("alice"))]), "age");
    let (_, u) = infer(&expr);
    // The anonymous record is closed, but field access expects an open row.
    // Unifying {age: ?a | ?r} with {name: String} should fail because
    // the closed row doesn't have `age`.
    assert!(
        u.has_errors(),
        "Accessing missing field on closed record should error"
    );
}

#[test]
fn infer_namespaced_list_member_uses_unprefixed_binding() {
    let mut env = TypeEnv::new();
    let scheme = TypeScheme::mono(Type::Function(FunctionType {
        params: vec![Type::Int],
        ret: Box::new(Type::Int),
        effects: EffectRow::pure(),
    }));
    env.register_module_type_scheme("Kea.List", "map", scheme, Effects::pure_deterministic());
    let expr = field_access(var("List"), "map");
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(
        ty,
        Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })
    );
}

#[test]
fn infer_namespaced_member_uses_registered_module_alias() {
    let mut env = TypeEnv::new();
    env.register_module_alias("List", "Pkg.List");
    env.register_module_type_scheme(
        "Pkg.List",
        "map",
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })),
        Effects::pure_deterministic(),
    );
    let expr = field_access(var("List"), "map");
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(
        ty,
        Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })
    );
}

#[test]
fn register_module_type_scheme_auto_registers_short_alias() {
    let mut env = TypeEnv::new();
    env.register_module_type_scheme(
        "Pkg.List",
        "map",
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })),
        Effects::pure_deterministic(),
    );
    assert!(env.has_qualified_module("List"));
    assert!(env.resolve_qualified("List", "map").is_some());
}

#[test]
fn infer_namespaced_map_member_prefers_exact_binding() {
    let mut env = TypeEnv::new();
    env.register_module_type_scheme(
        "Kea.Map",
        "get",
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })),
        Effects::pure_deterministic(),
    );
    env.register_module_type_scheme(
        "Kea.Map",
        "map_get",
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Bool],
            ret: Box::new(Type::Bool),
            effects: EffectRow::pure(),
        })),
        Effects::pure_deterministic(),
    );
    let expr = field_access(var("Map"), "get");
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(
        ty,
        Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })
    );
}

#[test]
fn infer_namespaced_unknown_module_reports_clear_error() {
    let expr = field_access(var("Foo"), "bar");
    let (_, u) = infer(&expr);
    let message = u
        .errors()
        .first()
        .map(|d| d.message.clone())
        .unwrap_or_default();
    assert!(
        message.contains("unknown module `Foo`"),
        "message was: {message}"
    );
}

#[test]
fn infer_namespaced_unknown_member_reports_clear_error() {
    let mut env = TypeEnv::new();
    env.register_module_function("Kea.List", "map");
    env.bind(
        "map".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })),
    );

    let expr = field_access(var("List"), "nonexistent");
    let (_, u) = infer_with_env(&expr, &mut env);
    let message = u
        .errors()
        .first()
        .map(|d| d.message.clone())
        .unwrap_or_default();
    assert!(
        message.contains("module List has no function `nonexistent`"),
        "message was: {message}"
    );
}

// ===========================================================================
// Row polymorphism via let-generalization
// ===========================================================================

#[test]
fn infer_row_polymorphic_field_access() {
    // { let get_name = |r| r.name; get_name(#{ name: "alice", age: 30 }) }
    //   →  String
    //
    // `get_name` should be generalized to `forall r. {name: a | r} -> a`
    // (or similar), allowing it to work on any record with a `name` field.
    let expr = block(vec![
        let_bind("get_name", lambda(&["r"], field_access(var("r"), "name"))),
        call(
            var("get_name"),
            vec![anon_record(vec![
                ("name", lit_str("alice")),
                ("age", lit_int(30)),
            ])],
        ),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::String);
}

#[test]
fn infer_row_polymorphic_multiple_uses() {
    // { let get_name = |r| r.name;
    //   #(get_name(#{ name: "alice", age: 30 }),
    //     get_name(#{ name: "bob", email: "b@b.com" })) }
    //   →  #(String, String)
    //
    // get_name works on records with different extra fields.
    let expr = block(vec![
        let_bind("get_name", lambda(&["r"], field_access(var("r"), "name"))),
        tuple(vec![
            call(
                var("get_name"),
                vec![anon_record(vec![
                    ("name", lit_str("alice")),
                    ("age", lit_int(30)),
                ])],
            ),
            call(
                var("get_name"),
                vec![anon_record(vec![
                    ("name", lit_str("bob")),
                    ("email", lit_str("b@b.com")),
                ])],
            ),
        ]),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Tuple(vec![Type::String, Type::String]));
}

// ===========================================================================
// Left-arg application helper
// ===========================================================================

#[test]
fn infer_left_arg_application() {
    // { let double = |x| x + x; double(21) }  -> Int
    let expr = block(vec![
        let_bind(
            "double",
            lambda(&["x"], binop(BinOp::Add, var("x"), var("x"))),
        ),
        apply_first_arg(lit_int(21), var("double")),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_left_arg_application_call_prepends_left_arg() {
    // { let pick_first = |a, b| a; pick_first(1, 2) } -> Int
    let expr = block(vec![
        let_bind("pick_first", lambda(&["a", "b"], var("a"))),
        apply_first_arg(lit_int(1), call(var("pick_first"), vec![lit_int(2)])),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Int);
}

// ===========================================================================
// Constructors: Some, Ok, Err
// ===========================================================================

#[test]
fn infer_some() {
    // Some(42)  →  Option(Int)
    let expr = constructor("Some", vec![lit_int(42)]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Option(Box::new(Type::Int)));
}

#[test]
fn infer_none() {
    // None  →  Option(?a) for some fresh var
    let expr = sp(ExprKind::None);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    match &ty {
        Type::Option(_) => {} // Good — inner is some fresh var
        _ => panic!("Expected Option, got {ty:?}"),
    }
}

#[test]
fn infer_ascription_refines_empty_list() {
    let expr = ascribe(
        list(vec![]),
        TypeAnnotation::Applied(
            "List".to_string(),
            vec![TypeAnnotation::Named("Int".to_string())],
        ),
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_ascription_type_mismatch_errors() {
    let expr = ascribe(lit_str("hello"), TypeAnnotation::Named("Int".to_string()));
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "expected ascription mismatch error");
    let msg = u
        .errors()
        .iter()
        .map(|d| d.message.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(
        msg.contains("type mismatch in `as` ascription"),
        "expected ascription diagnostic, got: {msg}"
    );
}

#[test]
fn infer_ascription_allows_forall_subsumption_for_polymorphic_binding() {
    let forall_id = TypeAnnotation::Forall {
        type_vars: vec!["a".to_string()],
        ty: Box::new(TypeAnnotation::Function(
            vec![TypeAnnotation::Named("a".to_string())],
            Box::new(TypeAnnotation::Named("a".to_string())),
        )),
    };
    let expr = block(vec![
        let_bind("id", lambda(&["x"], var("x"))),
        ascribe(var("id"), forall_id),
    ]);

    let (ty, u) = infer(&expr);
    assert!(
        !u.has_errors(),
        "forall ascription on polymorphic binding should pass: {:?}",
        u.errors()
    );
    assert!(
        matches!(ty, Type::Forall(_)),
        "expected forall type, got {ty:?}"
    );
}

#[test]
fn infer_ascription_rejects_forall_subsumption_for_monomorphic_binding() {
    let forall_id = TypeAnnotation::Forall {
        type_vars: vec!["a".to_string()],
        ty: Box::new(TypeAnnotation::Function(
            vec![TypeAnnotation::Named("a".to_string())],
            Box::new(TypeAnnotation::Named("a".to_string())),
        )),
    };
    let expr = block(vec![
        let_bind("const_one", lambda(&["x"], lit_int(1))),
        ascribe(var("const_one"), forall_id),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(
        u.has_errors(),
        "forall ascription on monomorphic binding should fail"
    );
}

#[test]
fn infer_precision_let_annotation_accepts_in_range_int_literal() {
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("x".to_string())),
            annotation: Some(sp(TypeAnnotation::Named("Int32".to_string()))),
            value: Box::new(lit_int(42)),
        }),
        var("x"),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(
        ty,
        Type::IntN(kea_types::IntWidth::I32, kea_types::Signedness::Signed)
    );
}

#[test]
fn infer_precision_let_annotation_rejects_out_of_range_int_literal() {
    let expr = sp(ExprKind::Let {
        pattern: sp(PatternKind::Var("x".to_string())),
        annotation: Some(sp(TypeAnnotation::Named("Int8".to_string()))),
        value: Box::new(lit_int(300)),
    });
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "expected out-of-range literal error");
    let msg = u
        .errors()
        .iter()
        .map(|d| d.message.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(
        msg.contains("does not fit in `Int8`"),
        "expected Int8 range diagnostic, got: {msg}"
    );
}

#[test]
fn infer_call_pushes_expected_precision_into_arguments() {
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let expr = call(var("narrow"), vec![lit_int(200)]);
    let mut env = TypeEnv::new();
    env.bind(
        "narrow".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![expected.clone()],
            ret: Box::new(expected),
            effects: EffectRow::pure(),
        })),
    );

    let (_ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        u.has_errors(),
        "expected out-of-range literal error in infer-mode call"
    );
    let msg = u
        .errors()
        .iter()
        .map(|d| d.message.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(
        msg.contains("does not fit in"),
        "expected precision-range diagnostic from infer-mode call arg, got: {msg}"
    );
}

#[test]
fn infer_left_arg_application_pushes_expected_precision_into_arguments() {
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let expr = apply_first_arg(lit_int(200), var("narrow"));
    let mut env = TypeEnv::new();
    env.bind(
        "narrow".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![expected.clone()],
            ret: Box::new(expected),
            effects: EffectRow::pure(),
        })),
    );

    let (_ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        u.has_errors(),
        "expected out-of-range literal error in infer-mode left-arg application"
    );
    let msg = u
        .errors()
        .iter()
        .map(|d| d.message.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(
        msg.contains("does not fit in"),
        "expected precision-range diagnostic from infer-mode left-arg application arg, got: {msg}"
    );
}

#[test]
fn infer_precision_lambda_return_annotation_accepts_float_literal() {
    let expr = sp(ExprKind::Lambda {
        params: vec![],
        body: Box::new(lit_float(3.25)),
        return_annotation: Some(sp(TypeAnnotation::Named("Float32".to_string()))),
    });
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(
        ty,
        Type::Function(FunctionType {
            params: vec![],
            ret: Box::new(Type::FloatN(kea_types::FloatWidth::F32)),
            effects: EffectRow::pure(),
        })
    );
}

#[test]
fn infer_rank2_forall_parameter_allows_polymorphic_callback() {
    let forall_id = TypeAnnotation::Forall {
        type_vars: vec!["a".to_string()],
        ty: Box::new(TypeAnnotation::Function(
            vec![TypeAnnotation::Named("a".to_string())],
            Box::new(TypeAnnotation::Named("a".to_string())),
        )),
    };

    let apply_both = sp(ExprKind::Lambda {
        params: vec![
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("f".to_string())),
                annotation: Some(sp(forall_id)),
                default: None,
            },
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("x".to_string())),
                annotation: Some(sp(TypeAnnotation::Named("Int".to_string()))),
                default: None,
            },
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("y".to_string())),
                annotation: Some(sp(TypeAnnotation::Named("String".to_string()))),
                default: None,
            },
        ],
        body: Box::new(tuple(vec![
            call(var("f"), vec![var("x")]),
            call(var("f"), vec![var("y")]),
        ])),
        return_annotation: None,
    });

    let expr = block(vec![
        let_bind("id", lambda(&["v"], var("v"))),
        let_bind("apply_both", apply_both),
        call(
            var("apply_both"),
            vec![var("id"), lit_int(1), lit_str("ok")],
        ),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Tuple(vec![Type::Int, Type::String]));
}

#[test]
fn infer_rank2_forall_parameter_rejects_monomorphic_callback() {
    let forall_id = TypeAnnotation::Forall {
        type_vars: vec!["a".to_string()],
        ty: Box::new(TypeAnnotation::Function(
            vec![TypeAnnotation::Named("a".to_string())],
            Box::new(TypeAnnotation::Named("a".to_string())),
        )),
    };

    let apply = sp(ExprKind::Lambda {
        params: vec![
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("f".to_string())),
                annotation: Some(sp(forall_id)),
                default: None,
            },
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("x".to_string())),
                annotation: Some(sp(TypeAnnotation::Named("Int".to_string()))),
                default: None,
            },
        ],
        body: Box::new(call(var("f"), vec![var("x")])),
        return_annotation: None,
    });

    let expr = block(vec![
        let_bind(
            "mono",
            lambda(&["n"], binop(BinOp::Add, var("n"), lit_int(1))),
        ),
        let_bind("apply", apply),
        call(var("apply"), vec![var("mono"), lit_int(7)]),
    ]);
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "expected rank-2 mismatch error");
    let msg = u
        .errors()
        .iter()
        .map(|d| d.message.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(
        msg.contains("not polymorphic enough"),
        "expected rank-2 diagnostic, got: {msg}"
    );
}

#[test]
fn infer_left_arg_application_rejects_monomorphic_callback_for_rank2_parameter() {
    let forall_id = TypeAnnotation::Forall {
        type_vars: vec!["a".to_string()],
        ty: Box::new(TypeAnnotation::Function(
            vec![TypeAnnotation::Named("a".to_string())],
            Box::new(TypeAnnotation::Named("a".to_string())),
        )),
    };

    let use_poly = sp(ExprKind::Lambda {
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: Some(sp(forall_id)),
            default: None,
        }],
        body: Box::new(call(var("f"), vec![lit_int(1)])),
        return_annotation: None,
    });

    let expr = block(vec![
        let_bind(
            "mono",
            lambda(&["n"], binop(BinOp::Add, var("n"), lit_int(1))),
        ),
        let_bind("use_poly", use_poly),
        apply_first_arg(var("mono"), var("use_poly")),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "expected rank-2 mismatch error");
    let msg = u
        .errors()
        .iter()
        .map(|d| d.message.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(
        msg.contains("not polymorphic enough"),
        "expected rank-2 diagnostic, got: {msg}"
    );
}

#[test]
fn infer_left_arg_application_accepts_polymorphic_callback_for_rank2_parameter() {
    let forall_id = TypeAnnotation::Forall {
        type_vars: vec!["a".to_string()],
        ty: Box::new(TypeAnnotation::Function(
            vec![TypeAnnotation::Named("a".to_string())],
            Box::new(TypeAnnotation::Named("a".to_string())),
        )),
    };

    let use_poly = sp(ExprKind::Lambda {
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: Some(sp(forall_id)),
            default: None,
        }],
        body: Box::new(call(var("f"), vec![lit_int(1)])),
        return_annotation: None,
    });

    let expr = block(vec![
        let_bind("id", lambda(&["v"], var("v"))),
        let_bind("use_poly", use_poly),
        apply_first_arg(var("id"), var("use_poly")),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(
        !u.has_errors(),
        "expected polymorphic callback to satisfy rank-2 left-arg application contract: {:?}",
        u.errors()
    );
}

#[test]
fn infer_left_arg_application_call_rejects_monomorphic_callback_for_rank2_parameter() {
    let forall_id = TypeAnnotation::Forall {
        type_vars: vec!["a".to_string()],
        ty: Box::new(TypeAnnotation::Function(
            vec![TypeAnnotation::Named("a".to_string())],
            Box::new(TypeAnnotation::Named("a".to_string())),
        )),
    };

    let use_poly_with = sp(ExprKind::Lambda {
        params: vec![
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("f".to_string())),
                annotation: Some(sp(forall_id)),
                default: None,
            },
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("x".to_string())),
                annotation: Some(sp(TypeAnnotation::Named("Int".to_string()))),
                default: None,
            },
        ],
        body: Box::new(call(var("f"), vec![var("x")])),
        return_annotation: None,
    });

    let expr = block(vec![
        let_bind(
            "mono",
            lambda(&["n"], binop(BinOp::Add, var("n"), lit_int(1))),
        ),
        let_bind("use_poly_with", use_poly_with),
        apply_first_arg(var("mono"), call(var("use_poly_with"), vec![lit_int(7)])),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "expected rank-2 mismatch error");
    let msg = u
        .errors()
        .iter()
        .map(|d| d.message.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(
        msg.contains("not polymorphic enough"),
        "expected rank-2 diagnostic, got: {msg}"
    );
}

#[test]
fn infer_left_arg_application_call_accepts_polymorphic_callback_for_rank2_parameter() {
    let forall_id = TypeAnnotation::Forall {
        type_vars: vec!["a".to_string()],
        ty: Box::new(TypeAnnotation::Function(
            vec![TypeAnnotation::Named("a".to_string())],
            Box::new(TypeAnnotation::Named("a".to_string())),
        )),
    };

    let use_poly_with = sp(ExprKind::Lambda {
        params: vec![
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("f".to_string())),
                annotation: Some(sp(forall_id)),
                default: None,
            },
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("x".to_string())),
                annotation: Some(sp(TypeAnnotation::Named("Int".to_string()))),
                default: None,
            },
        ],
        body: Box::new(call(var("f"), vec![var("x")])),
        return_annotation: None,
    });

    let expr = block(vec![
        let_bind("id", lambda(&["v"], var("v"))),
        let_bind("use_poly_with", use_poly_with),
        apply_first_arg(var("id"), call(var("use_poly_with"), vec![lit_int(7)])),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(
        !u.has_errors(),
        "expected polymorphic callback to satisfy rank-2 left-arg application call contract: {:?}",
        u.errors()
    );
}

#[test]
fn infer_ok() {
    // Ok(42)  →  Result(Int, ?e)
    let expr = constructor("Ok", vec![lit_int(42)]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    match &ty {
        Type::Result(ok, _) => assert_eq!(ok.as_ref(), &Type::Int),
        _ => panic!("Expected Result, got {ty:?}"),
    }
}

#[test]
fn infer_err() {
    // Err("oops")  →  Result(?t, String)
    let expr = constructor("Err", vec![lit_str("oops")]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    match &ty {
        Type::Result(_, err) => assert_eq!(err.as_ref(), &Type::String),
        _ => panic!("Expected Result, got {ty:?}"),
    }
}

// ===========================================================================
// Complex integration tests
// ===========================================================================

#[test]
fn infer_compose_functions() {
    // { let f = |x| x + 1;
    //   let g = |x| x * 2;
    //   f(g(3)) }
    //   →  Int
    let expr = block(vec![
        let_bind("f", lambda(&["x"], binop(BinOp::Add, var("x"), lit_int(1)))),
        let_bind("g", lambda(&["x"], binop(BinOp::Mul, var("x"), lit_int(2)))),
        call(var("f"), vec![call(var("g"), vec![lit_int(3)])]),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_higher_order_function() {
    // { let apply = |f, x| f(x); apply(|n| n + 1, 42) }  →  Int
    let expr = block(vec![
        let_bind("apply", lambda(&["f", "x"], call(var("f"), vec![var("x")]))),
        call(
            var("apply"),
            vec![
                lambda(&["n"], binop(BinOp::Add, var("n"), lit_int(1))),
                lit_int(42),
            ],
        ),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_polymorphic_higher_order() {
    // { let apply = |f, x| f(x);
    //   #(apply(|n| n + 1, 42),
    //     apply(|s| s, "hello")) }
    //   →  #(Int, String)
    let expr = block(vec![
        let_bind("apply", lambda(&["f", "x"], call(var("f"), vec![var("x")]))),
        tuple(vec![
            call(
                var("apply"),
                vec![
                    lambda(&["n"], binop(BinOp::Add, var("n"), lit_int(1))),
                    lit_int(42),
                ],
            ),
            call(
                var("apply"),
                vec![lambda(&["s"], var("s")), lit_str("hello")],
            ),
        ]),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Tuple(vec![Type::Int, Type::String]));
}

#[test]
fn infer_record_in_let_with_field_access() {
    // { let person = #{ name: "alice", age: 30 };
    //   person.age + 1 }
    //   →  Int
    let expr = block(vec![
        let_bind(
            "person",
            anon_record(vec![("name", lit_str("alice")), ("age", lit_int(30))]),
        ),
        binop(BinOp::Add, field_access(var("person"), "age"), lit_int(1)),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Int);
}

// ---------------------------------------------------------------------------
// Unary operators
// ---------------------------------------------------------------------------

#[test]
fn infer_negate_int() {
    let expr = unary(UnaryOp::Neg, lit_int(42));
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_negate_float() {
    let expr = unary(UnaryOp::Neg, lit_float(1.5));
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Float);
}

#[test]
fn infer_not_bool() {
    let expr = unary(UnaryOp::Not, lit_bool(true));
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Bool);
}

#[test]
fn infer_not_non_bool_error() {
    let expr = unary(UnaryOp::Not, lit_int(1));
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors());
}

// ---------------------------------------------------------------------------
// use expressions
// ---------------------------------------------------------------------------

#[test]
fn infer_use_result_chain_infers_result_type() {
    let expr = block(vec![
        use_expr(
            Some(sp(PatternKind::Var("x".to_string()))),
            constructor("Ok", vec![lit_int(41)]),
        ),
        constructor("Ok", vec![binop(BinOp::Add, var("x"), lit_int(1))]),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    match ty {
        Type::Result(ok, _) => assert_eq!(*ok, Type::Int),
        other => panic!("expected Result(Int, e), got {other:?}"),
    }
}

#[test]
fn infer_use_list_chain_infers_list_type() {
    let expr = block(vec![
        use_expr(
            Some(sp(PatternKind::Var("x".to_string()))),
            list(vec![lit_int(1), lit_int(2)]),
        ),
        list(vec![binop(BinOp::Add, var("x"), lit_int(1))]),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));
}

#[test]
fn infer_use_chain_records_desugared_annotation() {
    let head = use_expr(
        Some(sp(PatternKind::Var("x".to_string()))),
        list(vec![lit_int(1), lit_int(2)]),
    );
    let expr = block(vec![
        head.clone(),
        use_expr(
            Some(sp(PatternKind::Var("y".to_string()))),
            list(vec![var("x")]),
        ),
        list(vec![binop(BinOp::Add, var("x"), var("y"))]),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::List(Box::new(Type::Int)));

    let lowered = u
        .type_annotations
        .use_desugared
        .get(&head.span)
        .expect("expected lowered use annotation");
    let ExprKind::Call { func, .. } = &lowered.node else {
        panic!(
            "expected lowered use chain root to be a call, got {:?}",
            lowered.node
        );
    };
    let ExprKind::FieldAccess { expr, field } = &func.node else {
        panic!(
            "expected lowered use chain root call to target trait method, got {:?}",
            func.node
        );
    };
    assert_eq!(field.node, "bind");
    let ExprKind::Var(name) = &expr.node else {
        panic!(
            "expected trait receiver to be variable, got {:?}",
            expr.node
        );
    };
    assert_eq!(name, "Bind");
}

#[test]
fn infer_use_requires_continuation_expression() {
    let expr = block(vec![use_expr(
        Some(sp(PatternKind::Var("x".to_string()))),
        constructor("Some", vec![lit_int(1)]),
    )]);
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors());
    assert!(
        u.errors()
            .iter()
            .any(|d| d.message.contains("must be followed by a continuation")),
        "expected continuation diagnostic, got: {:?}",
        u.errors()
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );
}

#[test]
fn infer_use_outside_block_errors() {
    let expr = use_expr(
        Some(sp(PatternKind::Var("x".to_string()))),
        constructor("Some", vec![lit_int(1)]),
    );
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors());
    assert!(
        u.errors()
            .iter()
            .any(|d| d.message.contains("statement form")),
        "expected statement-form diagnostic, got: {:?}",
        u.errors()
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );
}

#[test]
fn infer_use_on_non_container_reports_use_specific_error() {
    let expr = block(vec![
        use_expr(Some(sp(PatternKind::Var("x".to_string()))), lit_int(1)),
        var("x"),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "plain values in use chains should error");
    assert_eq!(u.errors()[0].message, "cannot use `use` with `Int`");
    let help = u.errors()[0].help.as_deref().unwrap_or_default();
    assert!(
        help.contains("use `let`"),
        "expected let-binding suggestion, got: {help}"
    );
}

#[test]
fn infer_use_result_chain_error_type_mismatch_reports_use_diagnostic() {
    let expr = block(vec![
        use_expr(
            Some(sp(PatternKind::Var("x".to_string()))),
            constructor("Err", vec![lit_str("io")]),
        ),
        use_expr(
            Some(sp(PatternKind::Var("y".to_string()))),
            constructor("Err", vec![lit_int(404)]),
        ),
        tuple(vec![var("x"), var("y")]),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "mismatched Result error types should error");
    assert_eq!(
        u.errors()[0].message,
        "mismatched error types in `use` chain"
    );
}

#[test]
fn infer_use_result_chain_error_type_mismatch_includes_from_solver_detail() {
    let expr = block(vec![
        use_expr(
            Some(sp(PatternKind::Var("x".to_string()))),
            constructor("Err", vec![lit_str("io")]),
        ),
        use_expr(
            Some(sp(PatternKind::Var("y".to_string()))),
            constructor("Err", vec![lit_int(404)]),
        ),
        tuple(vec![var("x"), var("y")]),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "mismatched Result error types should error");
    let help = u.errors()[0].help.as_deref().unwrap_or_default();
    assert!(
        help.contains("`From`"),
        "expected From-projection mismatch detail, got: {help}"
    );
}

#[test]
fn infer_use_option_in_result_context_reports_conversion_hint() {
    let expr = block(vec![
        use_expr(
            Some(sp(PatternKind::Var("x".to_string()))),
            constructor("Err", vec![lit_str("fail")]),
        ),
        use_expr(
            Some(sp(PatternKind::Var("y".to_string()))),
            constructor("Some", vec![lit_int(1)]),
        ),
        var("y"),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(
        u.has_errors(),
        "Option inside Result use chain should error"
    );
    assert_eq!(
        u.errors()[0].message,
        "cannot use `use` with Option in a Result context"
    );
    let help = u.errors()[0].help.as_deref().unwrap_or_default();
    assert!(
        help.contains("Option.ok_or"),
        "expected conversion hint in diagnostic help, got: {help}"
    );
}

#[test]
fn infer_use_rejects_refutable_pattern() {
    let expr = block(vec![
        use_expr(
            Some(constructor_pattern(
                "Ok",
                vec![sp(PatternKind::Var("x".to_string()))],
            )),
            constructor("Ok", vec![lit_int(1)]),
        ),
        var("x"),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "refutable use pattern should error");
    let msg = &u.errors()[0].message;
    assert!(
        msg.contains("irrefutable pattern"),
        "expected irrefutable-pattern diagnostic, got: {msg}"
    );
}

// ---------------------------------------------------------------------------
// Case expressions
// ---------------------------------------------------------------------------

fn case_expr(scrutinee: Expr, arms: Vec<CaseArm>) -> Expr {
    sp(ExprKind::Case {
        scrutinee: Box::new(scrutinee),
        arms,
    })
}

fn arm(pattern: Pattern, body: Expr) -> CaseArm {
    CaseArm {
        pattern,
        guard: None,
        body,
    }
}

fn pat_wildcard() -> Pattern {
    sp(PatternKind::Wildcard)
}

fn pat_var(name: &str) -> Pattern {
    sp(PatternKind::Var(name.to_string()))
}

fn pat_int(n: i64) -> Pattern {
    sp(PatternKind::Lit(Lit::Int(n)))
}

fn pat_constructor(name: &str, args: Vec<Pattern>) -> Pattern {
    constructor_pattern(name, args)
}

fn pat_tuple(pats: Vec<Pattern>) -> Pattern {
    sp(PatternKind::Tuple(pats))
}

fn cond_expr(arms: Vec<CondArm>) -> Expr {
    sp(ExprKind::Cond { arms })
}

fn cond_arm(condition: Expr, body: Expr) -> CondArm {
    CondArm {
        span: condition.span.merge(body.span),
        condition: Box::new(condition),
        body: Box::new(body),
    }
}

fn cond_wildcard_arm(body: Expr) -> CondArm {
    let wildcard = sp(ExprKind::Wildcard);
    CondArm {
        span: wildcard.span.merge(body.span),
        condition: Box::new(wildcard),
        body: Box::new(body),
    }
}

#[test]
fn infer_case_literal_arms() {
    // case 42 { 1 => "one", _ => "other" } → String
    let expr = case_expr(
        lit_int(42),
        vec![
            arm(pat_int(1), lit_str("one")),
            arm(pat_wildcard(), lit_str("other")),
        ],
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(u.substitution.apply(&ty), Type::String);
}

#[test]
fn infer_case_var_binding() {
    // case 42 { n => n + 1 } → Int (n is bound to Int)
    let expr = case_expr(
        lit_int(42),
        vec![arm(pat_var("n"), binop(BinOp::Add, var("n"), lit_int(1)))],
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(u.substitution.apply(&ty), Type::Int);
}

#[test]
fn infer_case_option_destructure() {
    // case Some(42) { Some(x) => x, None => 0 } → Int
    let expr = case_expr(
        constructor("Some", vec![lit_int(42)]),
        vec![
            arm(pat_constructor("Some", vec![pat_var("x")]), var("x")),
            arm(pat_constructor("None", vec![]), lit_int(0)),
        ],
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(u.substitution.apply(&ty), Type::Int);
}

#[test]
fn infer_case_patterns_constrain_variable_scrutinee_type() {
    // fn (x) => case x { Some(n) => n, None => 0 } should infer Option(Int) -> Int
    let expr = lambda(
        &["x"],
        case_expr(
            var("x"),
            vec![
                arm(pat_constructor("Some", vec![pat_var("n")]), var("n")),
                arm(pat_constructor("None", vec![]), lit_int(0)),
            ],
        ),
    );
    let (ty, u) = infer(&expr);
    assert!(
        !u.has_errors(),
        "case over variable scrutinee should typecheck: {:?}",
        u.errors()
    );
    assert_eq!(
        u.substitution.apply(&ty),
        Type::Function(FunctionType {
            params: vec![Type::Option(Box::new(Type::Int))],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })
    );
}

#[test]
fn infer_case_pattern_builtin_constructor_arity_mismatch_errors() {
    let expr = case_expr(
        constructor("Some", vec![lit_int(42)]),
        vec![
            arm(pat_constructor("Some", vec![]), lit_int(0)),
            arm(pat_wildcard(), lit_int(1)),
        ],
    );

    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "pattern arity mismatch should error");
    assert!(
        u.errors().iter().any(|diag| {
            diag.message
                .contains("`Some` expects 1 argument in pattern, got 0")
        }),
        "expected pattern arity diagnostic, got: {:?}",
        u.errors()
    );
}

#[test]
fn infer_case_pattern_sum_constructor_arity_mismatch_errors() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    let pair = TypeDef {
        annotations: vec![],
        public: false,
        name: sp("Pair".to_string()),
        doc: None,
        params: vec![],
        variants: vec![TypeVariant {
            annotations: vec![],
            name: sp("Pair".to_string()),
            fields: vec![
                variant_field(TypeAnnotation::Named("Int".to_string())),
                variant_field(TypeAnnotation::Named("Bool".to_string())),
            ],
            where_clause: vec![],
        }],
        derives: vec![],
    };
    sums.register(&pair, &records)
        .expect("Pair should register");

    let mut env = TypeEnv::new();
    let mut unifier = Unifier::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let expr = case_expr(
        constructor("Pair", vec![lit_int(1), lit_bool(true)]),
        vec![
            arm(pat_constructor("Pair", vec![pat_var("x")]), var("x")),
            arm(pat_wildcard(), lit_int(0)),
        ],
    );
    let _ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(unifier.has_errors(), "pattern arity mismatch should error");
    assert!(
        unifier.errors().iter().any(|diag| {
            diag.message
                .contains("`Pair` expects 2 arguments in pattern, got 1")
        }),
        "expected sum pattern arity diagnostic, got: {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_case_tuple_destructure() {
    // case #(1, "hello") { #(a, b) => a } → Int
    let expr = case_expr(
        tuple(vec![lit_int(1), lit_str("hello")]),
        vec![arm(pat_tuple(vec![pat_var("a"), pat_var("b")]), var("a"))],
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(u.substitution.apply(&ty), Type::Int);
}

#[test]
fn infer_case_tuple_non_exhaustive_without_irrefutable_pattern() {
    // case #(1, 2) { #(1, 2) => 0 } is non-exhaustive over #(Int, Int)
    let expr = case_expr(
        tuple(vec![lit_int(1), lit_int(2)]),
        vec![arm(pat_tuple(vec![pat_int(1), pat_int(2)]), lit_int(0))],
    );
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "expected non-exhaustive error");
    assert!(
        u.errors()
            .iter()
            .any(|d| d.category == Category::NonExhaustive),
        "expected NonExhaustive diagnostic, got {:?}",
        u.errors()
    );
}

#[test]
fn infer_case_result_destructure() {
    // case Ok(42) { Ok(v) => v, Err(e) => 0 } → Int
    let expr = case_expr(
        constructor("Ok", vec![lit_int(42)]),
        vec![
            arm(pat_constructor("Ok", vec![pat_var("v")]), var("v")),
            arm(pat_constructor("Err", vec![pat_var("e")]), lit_int(0)),
        ],
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(u.substitution.apply(&ty), Type::Int);
}

#[test]
fn infer_case_arm_type_mismatch() {
    // case 1 { 1 => "a", 2 => 42 } → error (String ≠ Int)
    let expr = case_expr(
        lit_int(1),
        vec![arm(pat_int(1), lit_str("a")), arm(pat_int(2), lit_int(42))],
    );
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors());
}

#[test]
fn infer_case_wildcard() {
    // case "hello" { _ => 42 } → Int (wildcard doesn't constrain scrutinee)
    let expr = case_expr(lit_str("hello"), vec![arm(pat_wildcard(), lit_int(42))]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(u.substitution.apply(&ty), Type::Int);
}

#[test]
fn infer_case_nested_pattern() {
    // case Some(#(1, 2)) { Some(#(a, b)) => a + b, _ => 0 } → Int
    let expr = case_expr(
        constructor("Some", vec![tuple(vec![lit_int(1), lit_int(2)])]),
        vec![
            arm(
                pat_constructor("Some", vec![pat_tuple(vec![pat_var("a"), pat_var("b")])]),
                binop(BinOp::Add, var("a"), var("b")),
            ),
            arm(pat_wildcard(), lit_int(0)),
        ],
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(u.substitution.apply(&ty), Type::Int);
}

#[test]
fn infer_cond_literal_arms() {
    let expr = cond_expr(vec![
        cond_arm(binop(BinOp::Gt, lit_int(1), lit_int(2)), lit_str("no")),
        cond_wildcard_arm(lit_str("yes")),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "unexpected errors: {:?}", u.errors());
    assert_eq!(u.substitution.apply(&ty), Type::String);
}

#[test]
fn infer_cond_requires_catch_all() {
    let expr = cond_expr(vec![cond_arm(lit_bool(true), lit_int(1))]);
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "expected non-exhaustive cond error");
    assert!(
        u.errors()
            .iter()
            .any(|d| d.message.contains("non-exhaustive cond")),
        "expected non-exhaustive cond diagnostic, got {:?}",
        u.errors()
    );
}

#[test]
fn infer_cond_arm_type_mismatch() {
    let expr = cond_expr(vec![
        cond_arm(lit_bool(true), lit_int(1)),
        cond_wildcard_arm(lit_str("x")),
    ]);
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "expected arm type mismatch error");
}

// ===========================================================================
// RecordRegistry
// ===========================================================================

#[test]
fn record_registry_register_and_lookup() {
    let mut registry = RecordRegistry::new();
    let def = make_record_def(
        "User",
        vec![
            ("name", TypeAnnotation::Named("String".into())),
            ("age", TypeAnnotation::Named("Int".into())),
        ],
    );
    registry.register(&def).expect("register should succeed");
    let info = registry.lookup("User").expect("User should be registered");
    assert!(info.row.rest.is_none()); // closed row
    assert_eq!(info.row.fields.len(), 2);
}

#[test]
fn record_registry_to_type() {
    let mut registry = RecordRegistry::new();
    let def = make_record_def(
        "Point",
        vec![
            ("x", TypeAnnotation::Named("Float".into())),
            ("y", TypeAnnotation::Named("Float".into())),
        ],
    );
    registry.register(&def).expect("register should succeed");
    let ty = registry
        .to_type("Point")
        .expect("Point should produce a type");
    match ty {
        Type::Record(rec) => {
            assert_eq!(rec.name, "Point");
            assert_eq!(rec.row.fields.len(), 2);
        }
        _ => panic!("expected Record type, got {:?}", ty),
    }
}

#[test]
fn record_registry_registers_parametric_record_placeholders() {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_param_record_def(
            "Box",
            vec!["t"],
            vec![("value", TypeAnnotation::Named("t".into()))],
        ))
        .expect("register should succeed");
    let info = registry.lookup("Box").expect("Box should be registered");
    assert_eq!(info.params, vec!["t".to_string()]);
    assert_eq!(info.row.fields.len(), 1);
    assert!(matches!(info.row.fields[0].1, Type::Var(TypeVarId(0))));
}

#[test]
fn record_registry_unknown_returns_none() {
    let registry = RecordRegistry::new();
    assert!(registry.lookup("Missing").is_none());
    assert!(registry.to_type("Missing").is_none());
}

#[test]
fn record_registry_names() {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_record_def(
            "A",
            vec![("x", TypeAnnotation::Named("Int".into()))],
        ))
        .unwrap();
    registry
        .register(&make_record_def(
            "B",
            vec![("y", TypeAnnotation::Named("Float".into()))],
        ))
        .unwrap();
    let names: Vec<&str> = registry.names().collect();
    assert_eq!(names, vec!["A", "B"]);
}

#[test]
fn record_registry_duplicate_field_errors() {
    let mut registry = RecordRegistry::new();
    let result = registry.register(&make_record_def(
        "Bad",
        vec![
            ("x", TypeAnnotation::Named("Int".into())),
            ("y", TypeAnnotation::Named("Float".into())),
            ("x", TypeAnnotation::Named("String".into())),
        ],
    ));
    assert!(result.is_err(), "expected error for duplicate field `x`");
    let msg = result.unwrap_err().message;
    assert!(msg.contains("duplicate field `x`"), "got: {msg}");
    assert!(msg.contains("record `Bad`"), "got: {msg}");
}

#[test]
fn record_registry_no_duplicate_ok() {
    let mut registry = RecordRegistry::new();
    let result = registry.register(&make_record_def(
        "Good",
        vec![
            ("x", TypeAnnotation::Named("Int".into())),
            ("y", TypeAnnotation::Named("Float".into())),
        ],
    ));
    assert!(result.is_ok());
}

// ===========================================================================
// Annotation resolution with records
// ===========================================================================

#[test]
fn annotation_resolves_named_record() {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_record_def(
            "User",
            vec![
                ("name", TypeAnnotation::Named("String".into())),
                ("age", TypeAnnotation::Named("Int".into())),
            ],
        ))
        .unwrap();

    // { let x: User = #{ name: "Alice", age: 30 }  x }
    // Decision 10: assigning an anonymous record literal to a named record
    // annotation is a type error — must use `User { name: "Alice", age: 30 }`.
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("x".to_string())),
            annotation: Some(sp(TypeAnnotation::Named("User".into()))),
            value: Box::new(anon_record(vec![
                ("name", lit_str("Alice")),
                ("age", lit_int(30)),
            ])),
        }),
        var("x"),
    ]);
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(
        u.has_errors(),
        "anonymous record literal should not satisfy named record annotation"
    );
    let err_msg = u.errors()[0].message.to_lowercase();
    assert!(
        err_msg.contains("anonymous record"),
        "error should mention anonymous record, got: {}",
        u.errors()[0].message
    );
}

#[test]
fn annotation_rejects_anon_record_indirection_into_named_record() {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_record_def(
            "User",
            vec![
                ("name", TypeAnnotation::Named("String".into())),
                ("age", TypeAnnotation::Named("Int".into())),
            ],
        ))
        .unwrap();

    // { let tmp = #{ ... }  let x: User = tmp  x }
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("tmp".to_string())),
            annotation: None,
            value: Box::new(anon_record(vec![
                ("name", lit_str("Alice")),
                ("age", lit_int(30)),
            ])),
        }),
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("x".to_string())),
            annotation: Some(sp(TypeAnnotation::Named("User".into()))),
            value: Box::new(var("tmp")),
        }),
        var("x"),
    ]);
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(
        u.has_errors(),
        "indirect anonymous record should not satisfy named record annotation"
    );
    let err_msg = u.errors()[0].message.to_lowercase();
    assert!(
        err_msg.contains("anonymous record"),
        "error should mention anonymous record, got: {}",
        u.errors()[0].message
    );
}

#[test]
fn annotation_resolves_parametric_record_application() {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_param_record_def(
            "Box",
            vec!["t"],
            vec![("value", TypeAnnotation::Named("t".into()))],
        ))
        .unwrap();

    let ann = TypeAnnotation::Applied("Box".into(), vec![TypeAnnotation::Named("Int".into())]);
    let ty = resolve_annotation(&ann, &registry, None).expect("annotation should resolve");
    match ty {
        Type::Record(rec) => {
            assert_eq!(rec.name, "Box");
            assert_eq!(rec.params, vec![Type::Int]);
            assert_eq!(rec.row.get(&Label::new("value")), Some(&Type::Int));
        }
        other => panic!("expected record type, got {other:?}"),
    }
}

#[test]
fn annotation_rejects_bare_parametric_sum_name() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    sums.register(
        &make_type_def(
            "Either",
            vec!["L", "R"],
            vec![
                ("Left", vec![TypeAnnotation::Named("L".to_string())]),
                ("Right", vec![TypeAnnotation::Named("R".to_string())]),
            ],
        ),
        &records,
    )
    .expect("Either should register");

    let ann = TypeAnnotation::Named("Either".to_string());
    assert!(
        resolve_annotation(&ann, &records, Some(&sums)).is_none(),
        "bare parametric sum annotation should be rejected"
    );
}

#[test]
fn annotation_parametric_sum_arity_cases() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    sums.register(
        &make_type_def(
            "Either",
            vec!["L", "R"],
            vec![
                ("Left", vec![TypeAnnotation::Named("L".to_string())]),
                ("Right", vec![TypeAnnotation::Named("R".to_string())]),
            ],
        ),
        &records,
    )
    .expect("Either should register");

    let wrong = TypeAnnotation::Applied(
        "Either".to_string(),
        vec![TypeAnnotation::Named("Int".to_string())],
    );
    assert!(
        resolve_annotation(&wrong, &records, Some(&sums)).is_none(),
        "wrong-arity sum application should be rejected"
    );

    let ok = TypeAnnotation::Applied(
        "Either".to_string(),
        vec![
            TypeAnnotation::Named("Int".to_string()),
            TypeAnnotation::Named("String".to_string()),
        ],
    );
    let resolved =
        resolve_annotation(&ok, &records, Some(&sums)).expect("correct-arity sum should resolve");
    match resolved {
        Type::Sum(sum) => {
            assert_eq!(sum.name, "Either");
            assert_eq!(sum.type_args, vec![Type::Int, Type::String]);
        }
        other => panic!("expected sum type, got {other:?}"),
    }
}

#[test]
fn annotation_reports_parametric_sum_arity_mismatch_in_inference() {
    let records = RecordRegistry::new();
    let mut sums = SumTypeRegistry::new();
    sums.register(
        &make_type_def(
            "Either",
            vec!["L", "R"],
            vec![
                ("Left", vec![TypeAnnotation::Named("L".to_string())]),
                ("Right", vec![TypeAnnotation::Named("R".to_string())]),
            ],
        ),
        &records,
    )
    .expect("Either should register");

    for (annotation, expected_got) in [
        (TypeAnnotation::Named("Either".to_string()), 0usize),
        (
            TypeAnnotation::Applied(
                "Either".to_string(),
                vec![TypeAnnotation::Named("Int".to_string())],
            ),
            1usize,
        ),
    ] {
        let expr = block(vec![
            sp(ExprKind::Let {
                pattern: sp(PatternKind::Var("x".to_string())),
                annotation: Some(sp(annotation)),
                value: Box::new(constructor("Left", vec![lit_int(1)])),
            }),
            var("x"),
        ]);

        let mut env = TypeEnv::new();
        let mut traits = TraitRegistry::new();
        register_hkt_for_use_for_traits(&mut traits, &records);
        let mut unifier = Unifier::new();
        let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);

        assert!(
            unifier.errors().iter().any(|diag| {
                diag.category == Category::ArityMismatch
                    && diag
                        .message
                        .contains("type `Either` expects 2 type arguments")
                    && diag.message.contains(&format!("got {expected_got}"))
            }),
            "expected arity-mismatch diagnostic for got={expected_got}, got: {:?}",
            unifier.errors()
        );
    }
}

#[test]
fn builtin_constructor_arity_mismatch_rejected() {
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();

    // List(Int, Int) — too many args
    let ann = TypeAnnotation::Applied(
        "List".to_string(),
        vec![
            TypeAnnotation::Named("Int".to_string()),
            TypeAnnotation::Named("Int".to_string()),
        ],
    );
    assert!(
        resolve_annotation(&ann, &records, Some(&sums)).is_none(),
        "List(Int, Int) should be rejected"
    );

    // Map(Int) — too few args
    let ann = TypeAnnotation::Applied(
        "Map".to_string(),
        vec![TypeAnnotation::Named("Int".to_string())],
    );
    assert!(
        resolve_annotation(&ann, &records, Some(&sums)).is_none(),
        "Map(Int) should be rejected"
    );

    // Map(Int, Int, Int) — too many args
    let ann = TypeAnnotation::Applied(
        "Map".to_string(),
        vec![
            TypeAnnotation::Named("Int".to_string()),
            TypeAnnotation::Named("Int".to_string()),
            TypeAnnotation::Named("Int".to_string()),
        ],
    );
    assert!(
        resolve_annotation(&ann, &records, Some(&sums)).is_none(),
        "Map(Int, Int, Int) should be rejected"
    );

    // Result(Int) — too few args
    let ann = TypeAnnotation::Applied(
        "Result".to_string(),
        vec![TypeAnnotation::Named("Int".to_string())],
    );
    assert!(
        resolve_annotation(&ann, &records, Some(&sums)).is_none(),
        "Result(Int) should be rejected"
    );

    // Decimal(18) — too few args (needs precision + scale)
    let ann = TypeAnnotation::Applied("Decimal".to_string(), vec![TypeAnnotation::DimLiteral(18)]);
    assert!(
        resolve_annotation(&ann, &records, Some(&sums)).is_none(),
        "Decimal(18) should be rejected"
    );

    // List(Int) — correct arity, should resolve
    let ann = TypeAnnotation::Applied(
        "List".to_string(),
        vec![TypeAnnotation::Named("Int".to_string())],
    );
    assert_eq!(
        resolve_annotation(&ann, &records, Some(&sums)),
        Some(Type::List(Box::new(Type::Int))),
        "List(Int) should resolve"
    );
}

#[test]
fn builtin_constructor_arity_mismatch_produces_diagnostic() {
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();

    for (name, args, expected_arity, got_arity) in [
        ("List", vec!["Int", "String"], 1usize, 2usize),
        ("Map", vec!["Int"], 2, 1),
        ("Result", vec!["Int", "String", "Bool"], 2, 3),
    ] {
        let annotation = TypeAnnotation::Applied(
            name.to_string(),
            args.iter()
                .map(|a| TypeAnnotation::Named(a.to_string()))
                .collect(),
        );
        let expr = block(vec![
            sp(ExprKind::Let {
                pattern: sp(PatternKind::Var("x".to_string())),
                annotation: Some(sp(annotation)),
                value: Box::new(lit_int(42)),
            }),
            var("x"),
        ]);

        let mut env = TypeEnv::new();
        let mut traits = TraitRegistry::new();
        register_hkt_for_use_for_traits(&mut traits, &records);
        let mut unifier = Unifier::new();
        let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);

        assert!(
            unifier.errors().iter().any(|diag| {
                diag.category == Category::ArityMismatch
                    && diag.message.contains(&format!(
                        "type `{name}` expects {expected_arity} type argument"
                    ))
                    && diag.message.contains(&format!("got {got_arity}"))
            }),
            "expected arity-mismatch diagnostic for {name}({got_arity} args), got: {:?}",
            unifier.errors()
        );
    }
}

#[test]
fn annotation_resolves_precision_numeric_names() {
    let registry = RecordRegistry::new();

    assert_eq!(
        resolve_annotation(&TypeAnnotation::Named("Int32".into()), &registry, None),
        Some(Type::IntN(
            kea_types::IntWidth::I32,
            kea_types::Signedness::Signed
        ))
    );
    assert_eq!(
        resolve_annotation(&TypeAnnotation::Named("UInt16".into()), &registry, None),
        Some(Type::IntN(
            kea_types::IntWidth::I16,
            kea_types::Signedness::Unsigned
        ))
    );
    assert_eq!(
        resolve_annotation(&TypeAnnotation::Named("Float32".into()), &registry, None),
        Some(Type::FloatN(kea_types::FloatWidth::F32))
    );
    assert_eq!(
        resolve_annotation(
            &TypeAnnotation::Applied(
                "Decimal".into(),
                vec![
                    TypeAnnotation::DimLiteral(18),
                    TypeAnnotation::DimLiteral(2),
                ],
            ),
            &registry,
            None,
        ),
        Some(Type::Decimal {
            precision: Dim::Known(18),
            scale: Dim::Known(2),
        })
    );
}

#[test]
fn infer_bare_decimal_annotation_is_not_erased_to_generic_var() {
    let expr = sp(ExprKind::Lambda {
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("x".to_string())),
            annotation: Some(sp(TypeAnnotation::Named("Decimal".to_string()))),
            default: None,
        }],
        body: Box::new(var("x")),
        return_annotation: Some(sp(TypeAnnotation::Named("Decimal".to_string()))),
    });
    let (ty, u) = infer(&expr);
    assert!(
        !u.has_errors(),
        "decimal annotation should type-check, got {:?}",
        u.errors()
    );
    match ty {
        Type::Function(ft) => {
            assert!(
                matches!(ft.params.first(), Some(Type::Decimal { .. })),
                "expected decimal parameter type, got {:?}",
                ft.params
            );
            assert!(
                matches!(*ft.ret, Type::Decimal { .. }),
                "expected decimal return type, got {:?}",
                ft.ret
            );
        }
        other => panic!("expected function type, got {other:?}"),
    }
}

#[test]
fn infer_list_of_bare_decimal_annotation_typechecks() {
    let decimal_ann = TypeAnnotation::Named("Decimal".to_string());
    let list_decimal_ann = TypeAnnotation::Applied("List".to_string(), vec![decimal_ann]);
    let expr = sp(ExprKind::Lambda {
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("xs".to_string())),
            annotation: Some(sp(list_decimal_ann.clone())),
            default: None,
        }],
        body: Box::new(var("xs")),
        return_annotation: Some(sp(list_decimal_ann)),
    });
    let (ty, u) = infer(&expr);
    assert!(
        !u.has_errors(),
        "list(decimal) annotation should type-check, got {:?}",
        u.errors()
    );
    match ty {
        Type::Function(ft) => {
            assert!(
                matches!(ft.params.first(), Some(Type::List(inner)) if matches!(&**inner, Type::Decimal { .. })),
                "expected List(Decimal) parameter type, got {:?}",
                ft.params
            );
            assert!(
                matches!(ft.ret.as_ref(), Type::List(inner) if matches!(inner.as_ref(), Type::Decimal { .. })),
                "expected List(Decimal) return type, got {:?}",
                ft.ret
            );
        }
        other => panic!("expected function type, got {other:?}"),
    }
}

#[test]
fn dim_literal_in_non_dim_constructor_emits_diagnostic() {
    // List(1) should produce a clear error, not silently become a type variable.
    let ann = TypeAnnotation::Applied("List".to_string(), vec![TypeAnnotation::DimLiteral(1)]);
    let expr = sp(ExprKind::Lambda {
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("xs".to_string())),
            annotation: Some(sp(ann.clone())),
            default: None,
        }],
        body: Box::new(var("xs")),
        return_annotation: Some(sp(ann)),
    });
    let (_ty, u) = infer(&expr);
    assert!(u.has_errors(), "List(1) should produce a type error");
    assert!(
        u.errors().iter().any(|d| {
            d.message.contains("integer literal") && d.message.contains("not valid as a type")
        }),
        "expected dim-literal diagnostic, got: {:?}",
        u.errors()
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );
}

#[test]
fn anon_record_arg_to_named_record_param_errors() {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_record_def(
            "User",
            vec![
                ("name", TypeAnnotation::Named("String".into())),
                ("age", TypeAnnotation::Named("Int".into())),
            ],
        ))
        .unwrap();

    // { let f = |u: User| u.name  f(#{ name: "Alice", age: 30 }) }
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: None,
            value: Box::new(sp(ExprKind::Lambda {
                params: vec![kea_ast::Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("u".to_string())),
                    annotation: Some(sp(TypeAnnotation::Named("User".into()))),
                    default: None,
                }],
                body: Box::new(sp(ExprKind::FieldAccess {
                    expr: Box::new(var("u")),
                    field: sp("name".to_string()),
                })),
                return_annotation: None,
            })),
        }),
        sp(ExprKind::Call {
            func: Box::new(var("f")),
            args: vec![Argument {
                label: None,
                value: anon_record(vec![("name", lit_str("Alice")), ("age", lit_int(30))]),
            }],
        }),
    ]);
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(
        u.has_errors(),
        "anonymous record literal passed to named record param should error"
    );
    let err_msg = u.errors()[0].message.to_lowercase();
    assert!(
        err_msg.contains("anonymous record"),
        "error should mention anonymous record, got: {}",
        u.errors()[0].message
    );
}

#[test]
fn anon_record_var_arg_to_named_record_param_errors() {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_record_def(
            "User",
            vec![
                ("name", TypeAnnotation::Named("String".into())),
                ("age", TypeAnnotation::Named("Int".into())),
            ],
        ))
        .unwrap();

    // {
    //   let f = |u: User| u.name
    //   let tmp = #{ name: "Alice", age: 30 }
    //   f(tmp)
    // }
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: None,
            value: Box::new(sp(ExprKind::Lambda {
                params: vec![kea_ast::Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("u".to_string())),
                    annotation: Some(sp(TypeAnnotation::Named("User".into()))),
                    default: None,
                }],
                body: Box::new(sp(ExprKind::FieldAccess {
                    expr: Box::new(var("u")),
                    field: sp("name".to_string()),
                })),
                return_annotation: None,
            })),
        }),
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("tmp".to_string())),
            annotation: None,
            value: Box::new(anon_record(vec![
                ("name", lit_str("Alice")),
                ("age", lit_int(30)),
            ])),
        }),
        sp(ExprKind::Call {
            func: Box::new(var("f")),
            args: vec![Argument {
                label: None,
                value: var("tmp"),
            }],
        }),
    ]);
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(
        u.has_errors(),
        "indirect anonymous record passed to named record param should error"
    );
    let err_msg = u.errors()[0].message.to_lowercase();
    assert!(
        err_msg.contains("anonymous record"),
        "error should mention anonymous record, got: {}",
        u.errors()[0].message
    );
}

#[test]
fn lambda_return_annotation_rejects_anon_record_indirection() {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_record_def(
            "User",
            vec![
                ("name", TypeAnnotation::Named("String".into())),
                ("age", TypeAnnotation::Named("Int".into())),
            ],
        ))
        .unwrap();

    // | | -> User { let tmp = #{ ... }  tmp }
    let expr = sp(ExprKind::Lambda {
        params: vec![],
        body: Box::new(block(vec![
            sp(ExprKind::Let {
                pattern: sp(PatternKind::Var("tmp".to_string())),
                annotation: None,
                value: Box::new(anon_record(vec![
                    ("name", lit_str("Alice")),
                    ("age", lit_int(30)),
                ])),
            }),
            var("tmp"),
        ])),
        return_annotation: Some(sp(TypeAnnotation::Named("User".into()))),
    });

    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(
        u.has_errors(),
        "indirect anonymous record should not satisfy named return annotation"
    );
    let err_msg = u.errors()[0].message.to_lowercase();
    assert!(
        err_msg.contains("anonymous record"),
        "error should mention anonymous record, got: {}",
        u.errors()[0].message
    );
}

#[test]
fn ascription_rejects_anon_record_indirection_into_named_record() {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_record_def(
            "User",
            vec![
                ("name", TypeAnnotation::Named("String".into())),
                ("age", TypeAnnotation::Named("Int".into())),
            ],
        ))
        .unwrap();

    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("tmp".to_string())),
            annotation: None,
            value: Box::new(anon_record(vec![
                ("name", lit_str("Alice")),
                ("age", lit_int(30)),
            ])),
        }),
        sp(ExprKind::As {
            expr: Box::new(var("tmp")),
            annotation: sp(TypeAnnotation::Named("User".into())),
        }),
    ]);
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(
        u.has_errors(),
        "indirect anonymous record should not satisfy named ascription"
    );
    let err_msg = u.errors()[0].message.to_lowercase();
    assert!(
        err_msg.contains("anonymous record"),
        "error should mention anonymous record, got: {}",
        u.errors()[0].message
    );
}

#[test]
fn bare_record_annotation_creates_open_row() {
    // { let identity = |r: Record| r  identity }
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("identity".to_string())),
            annotation: None,
            value: Box::new(sp(ExprKind::Lambda {
                params: vec![kea_ast::Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("r".to_string())),
                    annotation: Some(sp(TypeAnnotation::Named("Record".into()))),
                    default: None,
                }],
                body: Box::new(var("r")),
                return_annotation: None,
            })),
        }),
        var("identity"),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "unexpected errors: {:?}", u.errors());
    let resolved = u.substitution.apply(&ty);
    match resolved {
        Type::Function(ft) => {
            assert!(matches!(ft.params[0], Type::AnonRecord(_)));
            match &ft.params[0] {
                Type::AnonRecord(row) => assert!(row.is_open()),
                _ => unreachable!(),
            }
        }
        other => panic!("expected Function type, got {other:?}"),
    }
}

#[test]
fn partial_type_op_wraps_record_fields_in_option() {
    let mut records = RecordRegistry::new();
    records
        .register(&make_record_def(
            "User",
            vec![
                ("name", TypeAnnotation::Named("String".into())),
                ("age", TypeAnnotation::Named("Int".into())),
            ],
        ))
        .unwrap();

    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: None,
            value: Box::new(sp(ExprKind::Lambda {
                params: vec![kea_ast::Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("u".to_string())),
                    annotation: Some(sp(TypeAnnotation::Applied(
                        "Partial".into(),
                        vec![TypeAnnotation::Named("User".into())],
                    ))),
                    default: None,
                }],
                body: Box::new(var("u")),
                return_annotation: None,
            })),
        }),
        var("f"),
    ]);

    let (ty, u) = infer_with_records(&expr, &records);
    assert!(!u.has_errors(), "unexpected errors: {:?}", u.errors());
    let resolved = u.substitution.apply(&ty);
    let expected_row = RowType::closed(vec![
        (Label::new("age"), Type::Option(Box::new(Type::Int))),
        (Label::new("name"), Type::Option(Box::new(Type::String))),
    ]);
    match resolved {
        Type::Function(ft) => {
            assert_eq!(ft.params[0], Type::AnonRecord(expected_row.clone()));
            assert_eq!(*ft.ret, Type::AnonRecord(expected_row));
        }
        other => panic!("expected Function type, got {other:?}"),
    }
}

#[test]
fn omit_type_op_drops_selected_fields() {
    let mut records = RecordRegistry::new();
    records
        .register(&make_record_def(
            "User",
            vec![
                ("name", TypeAnnotation::Named("String".into())),
                ("age", TypeAnnotation::Named("Int".into())),
                ("password", TypeAnnotation::Named("String".into())),
            ],
        ))
        .unwrap();

    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: None,
            value: Box::new(sp(ExprKind::Lambda {
                params: vec![kea_ast::Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("u".to_string())),
                    annotation: Some(sp(TypeAnnotation::Applied(
                        "Omit".into(),
                        vec![
                            TypeAnnotation::Named("User".into()),
                            TypeAnnotation::Named("password".into()),
                        ],
                    ))),
                    default: None,
                }],
                body: Box::new(var("u")),
                return_annotation: None,
            })),
        }),
        var("f"),
    ]);

    let (ty, u) = infer_with_records(&expr, &records);
    assert!(!u.has_errors(), "unexpected errors: {:?}", u.errors());
    let resolved = u.substitution.apply(&ty);
    let expected_row = RowType::closed(vec![
        (Label::new("age"), Type::Int),
        (Label::new("name"), Type::String),
    ]);
    match resolved {
        Type::Function(ft) => {
            assert_eq!(ft.params[0], Type::AnonRecord(expected_row.clone()));
            assert_eq!(*ft.ret, Type::AnonRecord(expected_row));
        }
        other => panic!("expected Function type, got {other:?}"),
    }
}

#[test]
fn merge_type_op_prefers_right_field_types() {
    let mut records = RecordRegistry::new();
    records
        .register(&make_record_def(
            "Base",
            vec![
                ("x", TypeAnnotation::Named("Int".into())),
                ("y", TypeAnnotation::Named("String".into())),
            ],
        ))
        .unwrap();
    records
        .register(&make_record_def(
            "Override",
            vec![
                ("y", TypeAnnotation::Named("Bool".into())),
                ("z", TypeAnnotation::Named("Int".into())),
            ],
        ))
        .unwrap();

    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: None,
            value: Box::new(sp(ExprKind::Lambda {
                params: vec![kea_ast::Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("r".to_string())),
                    annotation: Some(sp(TypeAnnotation::Applied(
                        "Merge".into(),
                        vec![
                            TypeAnnotation::Named("Base".into()),
                            TypeAnnotation::Named("Override".into()),
                        ],
                    ))),
                    default: None,
                }],
                body: Box::new(var("r")),
                return_annotation: None,
            })),
        }),
        var("f"),
    ]);

    let (ty, u) = infer_with_records(&expr, &records);
    assert!(!u.has_errors(), "unexpected errors: {:?}", u.errors());
    let resolved = u.substitution.apply(&ty);
    let expected_row = RowType::closed(vec![
        (Label::new("x"), Type::Int),
        (Label::new("y"), Type::Bool),
        (Label::new("z"), Type::Int),
    ]);
    match resolved {
        Type::Function(ft) => {
            assert_eq!(ft.params[0], Type::AnonRecord(expected_row.clone()));
            assert_eq!(*ft.ret, Type::AnonRecord(expected_row));
        }
        other => panic!("expected Function type, got {other:?}"),
    }
}

#[test]
fn resolve_existential_annotation_with_assoc_constraints() {
    let ann = TypeAnnotation::Existential {
        bounds: vec!["Show".into(), "Eq".into()],
        associated_types: vec![("Item".into(), TypeAnnotation::Named("Int".into()))],
    };
    let records = RecordRegistry::new();
    let resolved = resolve_annotation(&ann, &records, None).expect("annotation should resolve");

    let mut assoc = BTreeMap::new();
    assoc.insert("Item".to_string(), Type::Int);
    assert_eq!(
        resolved,
        Type::Existential {
            bounds: vec!["Show".into(), "Eq".into()],
            associated_types: assoc,
        }
    );
}

#[test]
fn existential_satisfies_its_own_bound_traits() {
    let traits = TraitRegistry::new();

    let existential = Type::Existential {
        bounds: vec!["Show".into()],
        associated_types: BTreeMap::new(),
    };

    assert!(has_unique_impl(&traits, "Show", existential.clone()));
    assert!(!has_unique_impl(&traits, "Eq", existential));
}

#[test]
fn annotation_unknown_type_name_produces_error() {
    // { let x: Unknown = 42  x }
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("x".to_string())),
            annotation: Some(sp(TypeAnnotation::Named("Unknown".into()))),
            value: Box::new(lit_int(42)),
        }),
        var("x"),
    ]);
    let (_ty, u) = infer(&expr);
    // Unknown type name should produce an error
    assert!(u.has_errors());
}

// ===========================================================================
// Named record construction (ExprKind::Record)
// ===========================================================================

fn named_record(name: &str, fields: Vec<(&str, Expr)>) -> Expr {
    sp(ExprKind::Record {
        name: sp(name.to_string()),
        fields: fields
            .into_iter()
            .map(|(n, e)| (sp(n.to_string()), e))
            .collect(),
        spread: None,
    })
}

fn named_record_spread(name: &str, fields: Vec<(&str, Expr)>, spread: Expr) -> Expr {
    sp(ExprKind::Record {
        name: sp(name.to_string()),
        fields: fields
            .into_iter()
            .map(|(n, e)| (sp(n.to_string()), e))
            .collect(),
        spread: Some(Box::new(spread)),
    })
}

fn user_registry() -> RecordRegistry {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_record_def(
            "User",
            vec![
                ("name", TypeAnnotation::Named("String".into())),
                ("age", TypeAnnotation::Named("Int".into())),
            ],
        ))
        .unwrap();
    registry
}

#[test]
fn record_construction_correct_fields() {
    let registry = user_registry();
    let expr = named_record(
        "User",
        vec![("name", lit_str("Alice")), ("age", lit_int(30))],
    );
    let (ty, u) = infer_with_records(&expr, &registry);
    assert!(!u.has_errors(), "expected no errors, got: {:?}", u.errors());
    match u.substitution.apply(&ty) {
        Type::Record(rec) => assert_eq!(rec.name, "User"),
        other => panic!("expected Record, got {other:?}"),
    }
}

#[test]
fn parametric_record_construction_infers_type_argument() {
    let mut registry = RecordRegistry::new();
    registry
        .register(&make_param_record_def(
            "Box",
            vec!["t"],
            vec![("value", TypeAnnotation::Named("t".into()))],
        ))
        .unwrap();

    let expr = named_record("Box", vec![("value", lit_int(42))]);
    let (ty, u) = infer_with_records(&expr, &registry);
    assert!(!u.has_errors(), "expected no errors, got: {:?}", u.errors());
    match u.substitution.apply(&ty) {
        Type::Record(rec) => {
            assert_eq!(rec.name, "Box");
            assert_eq!(rec.params, vec![Type::Int]);
            assert_eq!(rec.row.get(&Label::new("value")), Some(&Type::Int));
        }
        other => panic!("expected Record, got {other:?}"),
    }
}

#[test]
fn record_construction_wrong_field_type() {
    let registry = user_registry();
    // age should be Int, not String
    let expr = named_record(
        "User",
        vec![("name", lit_str("Alice")), ("age", lit_str("thirty"))],
    );
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(u.has_errors(), "expected type error for wrong field type");
}

#[test]
fn record_construction_missing_field() {
    let registry = user_registry();
    // Only provide name, missing age
    let expr = named_record("User", vec![("name", lit_str("Alice"))]);
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(u.has_errors(), "expected error for missing field");
}

#[test]
fn record_construction_extra_field() {
    let registry = user_registry();
    // Extra field 'email'
    let expr = named_record(
        "User",
        vec![
            ("name", lit_str("Alice")),
            ("age", lit_int(30)),
            ("email", lit_str("alice@example.com")),
        ],
    );
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(u.has_errors(), "expected error for extra field");
}

#[test]
fn record_construction_unknown_record() {
    let registry = RecordRegistry::new();
    let expr = named_record("Unknown", vec![("x", lit_int(1))]);
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(u.has_errors(), "expected error for unknown record type");
}

#[test]
fn record_construction_duplicate_field_errors() {
    let registry = user_registry();
    let expr = named_record(
        "User",
        vec![
            ("name", lit_str("Alice")),
            ("name", lit_str("Bob")),
            ("age", lit_int(30)),
        ],
    );
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(u.has_errors(), "expected error for duplicate field `name`");
    let err = &u.errors()[0];
    assert!(
        err.message.contains("duplicate field `name`"),
        "got: {}",
        err.message
    );
}

#[test]
fn record_construction_field_access() {
    let registry = user_registry();
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("u".to_string())),
            annotation: None,
            value: Box::new(named_record(
                "User",
                vec![("name", lit_str("Alice")), ("age", lit_int(30))],
            )),
        }),
        field_access(var("u"), "name"),
    ]);
    let (ty, u) = infer_with_records(&expr, &registry);
    assert!(!u.has_errors(), "expected no errors, got: {:?}", u.errors());
    assert_eq!(u.substitution.apply(&ty), Type::String);
}

#[test]
fn record_construction_with_spread() {
    let registry = user_registry();
    // User { age: 31, ..base } where base is a User
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("base".to_string())),
            annotation: None,
            value: Box::new(named_record(
                "User",
                vec![("name", lit_str("Alice")), ("age", lit_int(30))],
            )),
        }),
        named_record_spread("User", vec![("age", lit_int(31))], var("base")),
    ]);
    let (ty, u) = infer_with_records(&expr, &registry);
    assert!(!u.has_errors(), "expected no errors, got: {:?}", u.errors());
    match u.substitution.apply(&ty) {
        Type::Record(rec) => assert_eq!(rec.name, "User"),
        other => panic!("expected Record, got {other:?}"),
    }
}

// ===========================================================================
// Named record in pattern matching
// ===========================================================================

fn pat_record(name: &str, fields: Vec<(&str, kea_ast::Pattern)>, rest: bool) -> kea_ast::Pattern {
    sp(PatternKind::Record {
        name: name.to_string(),
        fields: fields
            .into_iter()
            .map(|(n, p)| (n.to_string(), p))
            .collect(),
        rest,
    })
}

#[test]
fn record_pattern_binds_fields() {
    let registry = user_registry();
    // case User { name: "Alice", age: 30 } { User { name: n, age: a } -> a }
    let scrutinee = named_record(
        "User",
        vec![("name", lit_str("Alice")), ("age", lit_int(30))],
    );
    let expr = sp(ExprKind::Case {
        scrutinee: Box::new(scrutinee),
        arms: vec![arm(
            pat_record(
                "User",
                vec![("name", pat_var("n")), ("age", pat_var("a"))],
                false,
            ),
            var("a"),
        )],
    });
    let (ty, u) = infer_with_records(&expr, &registry);
    assert!(!u.has_errors(), "expected no errors, got: {:?}", u.errors());
    assert_eq!(u.substitution.apply(&ty), Type::Int);
}

#[test]
fn record_pattern_non_exhaustive_when_field_pattern_is_refutable() {
    let registry = user_registry();
    let scrutinee = named_record(
        "User",
        vec![("name", lit_str("Alice")), ("age", lit_int(30))],
    );
    let expr = sp(ExprKind::Case {
        scrutinee: Box::new(scrutinee),
        arms: vec![arm(
            pat_record(
                "User",
                vec![
                    (
                        "name",
                        sp(PatternKind::Lit(Lit::String("Alice".to_string()))),
                    ),
                    ("age", pat_var("age")),
                ],
                false,
            ),
            var("age"),
        )],
    });
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(u.has_errors(), "expected non-exhaustive error");
    assert!(
        u.errors()
            .iter()
            .any(|d| d.category == Category::NonExhaustive),
        "expected NonExhaustive diagnostic, got {:?}",
        u.errors()
    );
}

#[test]
fn record_pattern_unknown_record_errors() {
    let registry = RecordRegistry::new();
    let scrutinee = anon_record(vec![("x", lit_int(1))]);
    let expr = sp(ExprKind::Case {
        scrutinee: Box::new(scrutinee),
        arms: vec![arm(
            pat_record("Unknown", vec![("x", pat_var("v"))], false),
            var("v"),
        )],
    });
    let (_ty, u) = infer_with_records(&expr, &registry);
    assert!(u.has_errors(), "expected error for unknown record pattern");
}

#[test]
fn structural_projection_named_record() {
    // A row-polymorphic function accessing .name should work on a User
    let registry = user_registry();
    // { let get_name = |r| r.name  let u = User { name: "Alice", age: 30 }  get_name(u) }
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("get_name".to_string())),
            annotation: None,
            value: Box::new(lambda(&["r"], field_access(var("r"), "name"))),
        }),
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("u".to_string())),
            annotation: None,
            value: Box::new(named_record(
                "User",
                vec![("name", lit_str("Alice")), ("age", lit_int(30))],
            )),
        }),
        call(var("get_name"), vec![var("u")]),
    ]);
    let (ty, u) = infer_with_records(&expr, &registry);
    assert!(!u.has_errors(), "expected no errors, got: {:?}", u.errors());
    assert_eq!(u.substitution.apply(&ty), Type::String);
}

#[test]
fn nominal_identity_preserved_after_field_access() {
    // After accessing a field on a named record, the record variable
    // should still be typed as the nominal type (User), not an anonymous row.
    // This is KERNEL §2.3: nominal for traits, structural for row poly.
    let registry = user_registry();
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("u".to_string())),
            annotation: None,
            value: Box::new(named_record(
                "User",
                vec![("name", lit_str("Alice")), ("age", lit_int(30))],
            )),
        }),
        // Access a field — triggers structural projection
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("_n".to_string())),
            annotation: None,
            value: Box::new(field_access(var("u"), "name")),
        }),
        // Return u — should still be Record(User, ...)
        var("u"),
    ]);
    let (ty, u) = infer_with_records(&expr, &registry);
    assert!(!u.has_errors(), "expected no errors, got: {:?}", u.errors());
    match u.substitution.apply(&ty) {
        Type::Record(rec) => assert_eq!(rec.name, "User"),
        other => panic!("expected Record(User, ...), got {other:?}"),
    }
}

// ===========================================================================
// TraitRegistry
// ===========================================================================

fn make_trait_def(name: &str, methods: Vec<TraitMethod>) -> kea_ast::TraitDef {
    kea_ast::TraitDef {
        public: false,
        name: sp(name.to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods,
    }
}

fn kind_star() -> KindAnnotation {
    KindAnnotation::Star
}

fn kind_arrow(lhs: KindAnnotation, rhs: KindAnnotation) -> KindAnnotation {
    let _ = lhs;
    let _ = rhs;
    KindAnnotation::Star
}

fn make_trait_method(
    name: &str,
    params: Vec<(&str, Option<TypeAnnotation>)>,
    ret: Option<TypeAnnotation>,
) -> TraitMethod {
    TraitMethod {
        name: sp(name.to_string()),
        params: params
            .into_iter()
            .map(|(n, ann)| Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var(n.to_string())),
                annotation: ann.map(sp),
                default: None,
            })
            .collect(),
        return_annotation: ret.map(sp),
        effect_annotation: None,
        where_clause: vec![],
        default_body: None,
        doc: None,
        span: s(),
    }
}

fn make_trait_method_with_default(
    name: &str,
    params: Vec<(&str, Option<TypeAnnotation>)>,
    ret: Option<TypeAnnotation>,
    default_body: Expr,
) -> TraitMethod {
    let mut method = make_trait_method(name, params, ret);
    method.default_body = Some(default_body);
    method
}

fn make_impl_block(trait_name: &str, type_name: &str, methods: Vec<FnDecl>) -> kea_ast::ImplBlock {
    kea_ast::ImplBlock {
        trait_name: sp(trait_name.to_string()),
        type_name: sp(type_name.to_string()),
        type_params: vec![],
        methods,
        control_type: None,
        where_clause: vec![],
    }
}

fn make_impl_block_with_params(
    trait_name: &str,
    type_name: &str,
    type_params: Vec<&str>,
    where_clause: Vec<kea_ast::WhereItem>,
    methods: Vec<FnDecl>,
) -> kea_ast::ImplBlock {
    kea_ast::ImplBlock {
        trait_name: sp(trait_name.to_string()),
        type_name: sp(type_name.to_string()),
        type_params: type_params.into_iter().map(|p| sp(p.to_string())).collect(),
        methods,
        control_type: None,
        where_clause,
    }
}

fn make_fn_decl(name: &str, params: Vec<&str>, body: Expr) -> FnDecl {
    FnDecl {
        annotations: vec![],
        public: false,
        name: sp(name.to_string()),
        doc: None,
        params: params
            .into_iter()
            .map(|n| Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var(n.to_string())),
                annotation: None,
                default: None,
            })
            .collect(),
        return_annotation: None,
        effect_annotation: None,
        body: body.clone(),
        span: s(),
        where_clause: Vec::new(),
        testing: None,
        testing_tags: Vec::new(),
    }
}

fn make_effect_decl(
    name: &str,
    type_params: Vec<&str>,
    operations: Vec<EffectOperation>,
) -> EffectDecl {
    EffectDecl {
        public: false,
        name: sp(name.to_string()),
        doc: None,
        type_params: type_params.into_iter().map(|p| p.to_string()).collect(),
        operations,
    }
}

fn make_effect_operation(name: &str, params: Vec<Param>, ret: TypeAnnotation) -> EffectOperation {
    EffectOperation {
        name: sp(name.to_string()),
        params,
        return_annotation: sp(ret),
        doc: None,
        span: s(),
    }
}

// ---------------------------------------------------------------------------
// Effect inference
// ---------------------------------------------------------------------------

#[test]
fn infer_fn_decl_effects_pure_for_arithmetic_body() {
    let env = TypeEnv::new();
    let fn_decl = make_fn_decl("add1", vec!["x"], binop(BinOp::Add, var("x"), lit_int(1)));
    let effects = infer_fn_decl_effects(&fn_decl, &env);
    assert_eq!(effects, Effects::pure_deterministic());
}

#[test]
fn infer_fn_decl_effects_impure_for_spawn() {
    let env = TypeEnv::new();
    let fn_decl = make_fn_decl(
        "start",
        vec![],
        sp(ExprKind::Spawn {
            value: Box::new(lit_int(1)),
            config: None,
        }),
    );
    let effects = infer_fn_decl_effects(&fn_decl, &env);
    assert_eq!(effects, Effects::impure());
}

#[test]
fn infer_fn_decl_effects_propagate_from_called_function() {
    let mut env = TypeEnv::new();
    env.set_function_effect("io_fn".to_string(), Effects::impure());
    let fn_decl = make_fn_decl("wrapper", vec![], call(var("io_fn"), vec![]));
    let effects = infer_fn_decl_effects(&fn_decl, &env);
    assert_eq!(effects, Effects::impure());
}

#[test]
fn infer_fn_decl_effect_row_does_not_inject_io_for_unknown_callback_call() {
    let env = TypeEnv::new();
    let fn_decl = make_fn_decl("apply", vec!["f", "x"], call(var("f"), vec![var("x")]));
    let row = infer_fn_decl_effect_row(&fn_decl, &env);
    assert!(
        !row.row.has(&Label::new("IO")),
        "expected no phantom IO in inferred callback effect row, got {row:?}"
    );
    assert!(
        row.row.rest.is_some(),
        "unknown callback effects should stay open, got {row:?}"
    );
}

#[test]
fn infer_fn_decl_effects_uses_pure_callback_param_annotation() {
    let env = TypeEnv::new();
    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("apply".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: Some(sp(TypeAnnotation::FunctionWithEffect(
                vec![TypeAnnotation::Named("Int".to_string())],
                sp(EffectAnnotation::Pure),
                Box::new(TypeAnnotation::Named("Int".to_string())),
            ))),
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: call(var("f"), vec![lit_int(1)]),
        span: s(),
        where_clause: vec![],
        testing: None,
        testing_tags: Vec::new(),
    };
    let effects = infer_fn_decl_effects(&fn_decl, &env);
    assert_eq!(effects, Effects::pure_deterministic());
}

#[test]
fn infer_fn_decl_effects_uses_forall_wrapped_pure_callback_param_annotation() {
    let env = TypeEnv::new();
    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("apply".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: Some(sp(TypeAnnotation::Forall {
                type_vars: vec!["a".to_string()],
                ty: Box::new(TypeAnnotation::FunctionWithEffect(
                    vec![TypeAnnotation::Named("a".to_string())],
                    sp(EffectAnnotation::Pure),
                    Box::new(TypeAnnotation::Named("a".to_string())),
                )),
            })),
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: call(var("f"), vec![lit_int(1)]),
        span: s(),
        where_clause: vec![],
        testing: None,
        testing_tags: Vec::new(),
    };
    let effects = infer_fn_decl_effects(&fn_decl, &env);
    assert_eq!(effects, Effects::pure_deterministic());
}

#[test]
fn register_fn_effect_signature_skips_legacy_impure_annotation() {
    let mut env = TypeEnv::new();
    let mut fn_decl = make_fn_decl("legacy", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(EffectAnnotation::Impure));
    register_fn_effect_signature(&fn_decl, &mut env);
    assert!(env.function_effect_signature("legacy").is_none());
}

#[test]
fn register_effect_decl_exposes_qualified_operation_scheme() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("String".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );

    let diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
    assert!(env.resolve_qualified("Log", "log").is_some());
}

#[test]
fn effect_operation_call_infers_declared_effect_label() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("String".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let wrapper = make_fn_decl(
        "wrapper",
        vec![],
        call(field_access(var("Log"), "log"), vec![lit_str("hello")]),
    );
    let row = infer_fn_decl_effect_row(&wrapper, &env);
    assert!(
        row.row.has(&Label::new("Log")),
        "expected wrapper effects to include Log, got {row:?}"
    );

    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &wrapper.body,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &sums,
    );
    assert_eq!(ty, Type::Unit);
    assert!(!unifier.has_errors(), "type errors: {:?}", unifier.errors());
}

#[test]
fn fail_operation_call_infers_fail_payload_type_from_argument() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let fail = make_effect_decl(
        "Fail",
        vec!["E"],
        vec![make_effect_operation(
            "fail",
            vec![annotated_param(
                "error",
                TypeAnnotation::Named("E".to_string()),
            )],
            TypeAnnotation::Named("Never".to_string()),
        )],
    );
    let diags = register_effect_decl(&fail, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let wrapper = make_fn_decl(
        "wrapper",
        vec![],
        call(field_access(var("Fail"), "fail"), vec![lit_str("bad")]),
    );
    let row = infer_fn_decl_effect_row(&wrapper, &env);
    let fail_payload = row
        .row
        .fields
        .iter()
        .find(|(label, _)| label == &Label::new("Fail"))
        .map(|(_, payload)| payload.clone());
    assert_eq!(
        fail_payload,
        Some(Type::String),
        "expected Fail.fail(\"bad\") to infer `Fail String`, got {row:?}"
    );
}

#[test]
fn curried_annotated_callback_param_uses_effect_row_unification_not_pure_function_unification() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("Int".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let apply = sp(ExprKind::Lambda {
        params: vec![annotated_param(
            "f",
            TypeAnnotation::FunctionWithEffect(
                vec![TypeAnnotation::Named("Int".to_string())],
                sp(effect_row_annotation(vec![("Log", None)], None)),
                Box::new(TypeAnnotation::Named("Unit".to_string())),
            ),
        )],
        body: Box::new(sp(ExprKind::Lambda {
            params: vec![annotated_param(
                "x",
                TypeAnnotation::Named("Int".to_string()),
            )],
            body: Box::new(call(var("f"), vec![var("x")])),
            return_annotation: Some(sp(TypeAnnotation::Named("Unit".to_string()))),
        })),
        return_annotation: None,
    });
    let logger = sp(ExprKind::Lambda {
        params: vec![annotated_param(
            "y",
            TypeAnnotation::Named("Int".to_string()),
        )],
        body: Box::new(call(field_access(var("Log"), "log"), vec![var("y")])),
        return_annotation: Some(sp(TypeAnnotation::Named("Unit".to_string()))),
    });

    let trap = make_fn_decl(
        "trap",
        vec![],
        block(vec![
            let_bind("apply", apply),
            let_bind("logger", logger),
            call(call(var("apply"), vec![var("logger")]), vec![lit_int(42)]),
        ]),
    );

    let row = infer_fn_decl_effect_row(&trap, &env);
    assert!(
        row.row.has(&Label::new("Log")),
        "expected curried annotated callback to preserve Log, got {row:?}"
    );
    assert!(
        !row.row.has(&Label::new("IO")),
        "expected no phantom IO from annotated curried callback, got {row:?}"
    );

    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&trap.body, &mut env, &mut unifier, &records, &traits, &sums);
    assert_eq!(ty, Type::Unit);
    assert!(
        !unifier.has_errors(),
        "expected annotated curried callback to typecheck without row-mismatch diagnostics, got {:?}",
        unifier.errors()
    );
}

#[test]
fn curried_unannotated_callback_application_propagates_effect_row_from_argument() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("Int".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let apply = lambda(&["f"], lambda(&["x"], call(var("f"), vec![var("x")])));
    let logger = sp(ExprKind::Lambda {
        params: vec![annotated_param(
            "y",
            TypeAnnotation::Named("Int".to_string()),
        )],
        body: Box::new(call(field_access(var("Log"), "log"), vec![var("y")])),
        return_annotation: Some(sp(TypeAnnotation::Named("Unit".to_string()))),
    });
    let trap = make_fn_decl(
        "trap",
        vec![],
        block(vec![
            let_bind("apply", apply),
            let_bind("logger", logger),
            call(call(var("apply"), vec![var("logger")]), vec![lit_int(42)]),
        ]),
    );

    let row = infer_fn_decl_effect_row(&trap, &env);
    assert!(
        row.row.has(&Label::new("Log")),
        "expected unannotated curried callback to preserve Log, got {row:?}"
    );
    assert!(
        !row.row.has(&Label::new("IO")),
        "expected no phantom IO from unannotated curried callback, got {row:?}"
    );

    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&trap.body, &mut env, &mut unifier, &records, &traits, &sums);
    assert_eq!(ty, Type::Unit);
    assert!(
        !unifier.has_errors(),
        "expected unannotated curried callback to typecheck, got {:?}",
        unifier.errors()
    );
}

#[test]
fn handle_expression_removes_handled_effect_from_row() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("String".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let handled = call(field_access(var("Log"), "log"), vec![lit_str("hello")]);
    let clause = handle_clause(
        "Log",
        "log",
        vec![sp(PatternKind::Var("msg".to_string()))],
        resume(lit_unit()),
    );
    let wrapper = make_fn_decl("wrapper", vec![], handle_expr(handled, vec![clause], None));

    let row = infer_fn_decl_effect_row(&wrapper, &env);
    assert!(
        !row.row.has(&Label::new("Log")),
        "expected handled Log effect to be removed, got {row:?}"
    );

    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &wrapper.body,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &sums,
    );
    assert_eq!(ty, Type::Unit);
    assert!(!unifier.has_errors(), "type errors: {:?}", unifier.errors());
}

#[test]
fn nested_handlers_shadow_same_effect() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("String".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let inner = handle_expr(
        call(field_access(var("Log"), "log"), vec![lit_str("inner")]),
        vec![handle_clause(
            "Log",
            "log",
            vec![sp(PatternKind::Var("msg".to_string()))],
            call(field_access(var("Log"), "log"), vec![lit_str("nested")]),
        )],
        None,
    );
    let outer = handle_expr(
        inner,
        vec![handle_clause(
            "Log",
            "log",
            vec![sp(PatternKind::Var("msg".to_string()))],
            resume(lit_unit()),
        )],
        None,
    );
    let wrapper = make_fn_decl("wrapper", vec![], outer);

    let row = infer_fn_decl_effect_row(&wrapper, &env);
    assert!(
        !row.row.has(&Label::new("Log")),
        "expected outer handler to remove Log after inner shadowing, got {row:?}"
    );
}

#[test]
fn handler_effect_union_is_idempotent_for_residual_trace() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("String".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let trace = make_effect_decl(
        "Trace",
        vec![],
        vec![make_effect_operation(
            "emit",
            vec![annotated_param(
                "value",
                TypeAnnotation::Named("Int".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let log_diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(
        log_diags.is_empty(),
        "unexpected diagnostics: {log_diags:?}"
    );
    let trace_diags = register_effect_decl(&trace, &records, Some(&sums), &mut env);
    assert!(
        trace_diags.is_empty(),
        "unexpected diagnostics: {trace_diags:?}"
    );

    let handled = block(vec![
        call(field_access(var("Trace"), "emit"), vec![lit_int(0)]),
        call(field_access(var("Log"), "log"), vec![lit_str("hello")]),
    ]);
    let clause = handle_clause(
        "Log",
        "log",
        vec![sp(PatternKind::Var("msg".to_string()))],
        call(field_access(var("Trace"), "emit"), vec![lit_int(1)]),
    );
    let wrapper = make_fn_decl("wrapper", vec![], handle_expr(handled, vec![clause], None));

    let row = infer_fn_decl_effect_row(&wrapper, &env);
    let trace_label = Label::new("Trace");
    let trace_count = row
        .row
        .fields
        .iter()
        .filter(|(label, _)| label == &trace_label)
        .count();
    assert_eq!(
        trace_count, 1,
        "expected idempotent Trace union in handler effect row, got {row:?}"
    );
    assert!(
        !row.row.has(&Label::new("Log")),
        "expected handled Log effect to be removed, got {row:?}"
    );
}

#[test]
fn resume_outside_handler_is_type_error() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let expr = resume(lit_unit());
    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        unifier.errors().iter().any(|d| d
            .message
            .contains("only valid inside a matching handler clause")),
        "expected resume-outside-handler diagnostic, got {:?}",
        unifier.errors()
    );
}

#[test]
fn handler_clause_rejects_multiple_resumes() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("String".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let handled = call(field_access(var("Log"), "log"), vec![lit_str("hello")]);
    let clause = handle_clause(
        "Log",
        "log",
        vec![sp(PatternKind::Var("msg".to_string()))],
        block(vec![resume(lit_unit()), resume(lit_unit())]),
    );
    let expr = handle_expr(handled, vec![clause], None);

    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("may resume at most once")),
        "expected at-most-once resume diagnostic, got {:?}",
        unifier.errors()
    );
}

#[test]
fn handler_clause_rejects_resume_captured_in_lambda() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("String".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let handled = call(field_access(var("Log"), "log"), vec![lit_str("hello")]);
    let clause = handle_clause(
        "Log",
        "log",
        vec![sp(PatternKind::Var("msg".to_string()))],
        lambda(&["ignored"], resume(lit_unit())),
    );
    let expr = handle_expr(handled, vec![clause], None);

    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("cannot be captured in a lambda")),
        "expected resume-captured-in-lambda diagnostic, got {:?}",
        unifier.errors()
    );
}

#[test]
fn handler_clause_rejects_resume_inside_loop() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("String".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let handled = call(field_access(var("Log"), "log"), vec![lit_str("hello")]);
    let loop_body = for_expr(
        vec![for_gen(
            sp(PatternKind::Var("x".to_string())),
            list(vec![lit_int(1)]),
        )],
        resume(lit_unit()),
    );
    let clause = handle_clause(
        "Log",
        "log",
        vec![sp(PatternKind::Var("msg".to_string()))],
        loop_body,
    );
    let expr = handle_expr(handled, vec![clause], None);

    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("not allowed inside loops")),
        "expected resume-in-loop diagnostic, got {:?}",
        unifier.errors()
    );
}

#[test]
fn handler_clause_resume_value_must_match_operation_return() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let counter = make_effect_decl(
        "Counter",
        vec![],
        vec![make_effect_operation(
            "next",
            vec![],
            TypeAnnotation::Named("Int".to_string()),
        )],
    );
    let diags = register_effect_decl(&counter, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let handled = call(field_access(var("Counter"), "next"), vec![]);
    let clause = handle_clause("Counter", "next", vec![], resume(lit_str("bad")));
    let expr = handle_expr(handled, vec![clause], None);

    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    let msg = format!("{:?}", unifier.errors());
    assert!(unifier.has_errors(), "expected resume type mismatch");
    assert!(
        msg.contains("Int") && msg.contains("String"),
        "expected mismatch between Int and String, got {msg}"
    );
}

#[test]
fn handle_requires_clauses_for_all_effect_operations() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let net = make_effect_decl(
        "Net",
        vec![],
        vec![
            make_effect_operation("open", vec![], TypeAnnotation::Named("Unit".to_string())),
            make_effect_operation("close", vec![], TypeAnnotation::Named("Unit".to_string())),
        ],
    );
    let diags = register_effect_decl(&net, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let handled = call(field_access(var("Net"), "open"), vec![]);
    let clause = handle_clause("Net", "open", vec![], resume(lit_unit()));
    let expr = handle_expr(handled, vec![clause], None);

    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("missing clause(s): close")),
        "expected missing operation clause diagnostic, got {:?}",
        unifier.errors()
    );
}

#[test]
fn catch_style_handle_typechecks_to_result_and_removes_fail() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);
    let fail_effect = make_effect_decl(
        "Fail",
        vec!["E"],
        vec![make_effect_operation(
            "fail",
            vec![annotated_param(
                "error",
                TypeAnnotation::Named("E".to_string()),
            )],
            TypeAnnotation::Named("Int".to_string()),
        )],
    );
    let diags = register_effect_decl(&fail_effect, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let handled = call(field_access(var("Fail"), "fail"), vec![lit_str("boom")]);
    let clause = handle_clause(
        "Fail",
        "fail",
        vec![sp(PatternKind::Var("error".to_string()))],
        constructor("Err", vec![var("error")]),
    );
    let then_clause = lambda(&["value"], constructor("Ok", vec![var("value")]));
    let expr = handle_expr(handled, vec![clause], Some(then_clause));

    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    match ty {
        Type::Result(ok, _) => assert_eq!(*ok, Type::Int, "expected Ok payload to stay Int"),
        other => panic!("expected Result type from catch-style handler, got {other:?}"),
    }
    assert!(!unifier.has_errors(), "type errors: {:?}", unifier.errors());

    let fn_decl = make_fn_decl("wrapper", vec![], expr.clone());
    let row = infer_fn_decl_effect_row(&fn_decl, &env);
    assert!(
        !row.row.has(&Label::new("Fail")),
        "expected handled Fail effect to be removed, got {row:?}"
    );
}

#[test]
fn catch_reports_error_when_body_cannot_fail() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let clause = handle_clause(
        "Fail",
        "fail",
        vec![sp(PatternKind::Var("error".to_string()))],
        constructor("Err", vec![var("error")]),
    );
    let then_clause = lambda(&["value"], constructor("Ok", vec![var("value")]));
    let expr = handle_expr(lit_int(42), vec![clause], Some(then_clause));

    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        unifier.errors().iter().any(|d| d
            .message
            .contains("expression cannot fail; catch is unnecessary")),
        "expected catch precondition diagnostic, got {:?}",
        unifier.errors()
    );
    assert!(
        !unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("has no operation `fail`")),
        "catch precondition should short-circuit missing-operation fallback, got {:?}",
        unifier.errors()
    );
}

#[test]
fn catch_reports_error_when_body_has_non_fail_effects_only() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let log_row = EffectRow::closed(vec![(Label::new("Log"), Type::Unit)]);
    env.bind(
        "pureish".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![],
            ret: Box::new(Type::Int),
            effects: log_row.clone(),
        })),
    );
    env.set_function_effect_row("pureish".to_string(), log_row);

    let clause = handle_clause(
        "Fail",
        "fail",
        vec![sp(PatternKind::Var("error".to_string()))],
        constructor("Err", vec![var("error")]),
    );
    let then_clause = lambda(&["value"], constructor("Ok", vec![var("value")]));
    let expr = handle_expr(
        call(var("pureish"), vec![]),
        vec![clause],
        Some(then_clause),
    );

    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        unifier.errors().iter().any(|d| d
            .message
            .contains("expression cannot fail; catch is unnecessary")),
        "expected catch precondition diagnostic, got {:?}",
        unifier.errors()
    );
}

#[test]
fn catch_with_log_and_fail_preserves_log_and_removes_fail() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let fail_effect = make_effect_decl(
        "Fail",
        vec!["E"],
        vec![make_effect_operation(
            "fail",
            vec![annotated_param(
                "error",
                TypeAnnotation::Named("E".to_string()),
            )],
            TypeAnnotation::Named("Never".to_string()),
        )],
    );
    let diags = register_effect_decl(&fail_effect, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let with_fail_effects = EffectRow::closed(vec![
        (Label::new("Log"), Type::Unit),
        (Label::new("Fail"), Type::String),
    ]);
    env.bind(
        "with_fail".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![],
            ret: Box::new(Type::Int),
            effects: with_fail_effects.clone(),
        })),
    );
    env.set_function_effect_row("with_fail".to_string(), with_fail_effects);
    env.set_function_effect_signature(
        "with_fail".to_string(),
        FunctionEffectSignature {
            param_effect_rows: vec![],
            effect_row: EffectRow::closed(vec![
                (Label::new("Log"), Type::Unit),
                (Label::new("Fail"), Type::String),
            ]),
            instantiate_on_call: false,
        },
    );

    let clause = handle_clause(
        "Fail",
        "fail",
        vec![sp(PatternKind::Var("error".to_string()))],
        constructor("Err", vec![var("error")]),
    );
    let then_clause = lambda(&["value"], constructor("Ok", vec![var("value")]));
    let expr = handle_expr(
        call(var("with_fail"), vec![]),
        vec![clause],
        Some(then_clause),
    );

    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        matches!(ty, Type::Result(ref ok, _) if **ok == Type::Int),
        "expected catch to return Result(Int, _), got {ty:?}"
    );
    assert!(!unifier.has_errors(), "type errors: {:?}", unifier.errors());

    let wrapper = make_fn_decl("wrapper", vec![], expr);
    let row = infer_fn_decl_effect_row(&wrapper, &env);
    assert!(
        row.row.has(&Label::new("Log")),
        "expected Log to remain, got {row:?}"
    );
    assert!(
        !row.row.has(&Label::new("Fail")),
        "expected Fail to be removed, got {row:?}"
    );
}

#[test]
fn catch_over_higher_order_fail_parameter_is_accepted() {
    // Regression: `catch f()` where `f: fn() -[Fail String]> Int` was
    // rejected with E0012 because the main type-checker env didn't seed
    // function-typed parameter effect signatures.
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let fail_effect = make_effect_decl(
        "Fail",
        vec!["E"],
        vec![make_effect_operation(
            "fail",
            vec![annotated_param(
                "error",
                TypeAnnotation::Named("E".to_string()),
            )],
            TypeAnnotation::Named("Never".to_string()),
        )],
    );
    let diags = register_effect_decl(&fail_effect, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    // Build: fn wrap(f: fn() -[Fail String]> Int) -> Result(Int, String) = catch f()
    let param = Param {
        label: ParamLabel::Implicit,
        pattern: sp(PatternKind::Var("f".to_string())),
        annotation: Some(sp(TypeAnnotation::FunctionWithEffect(
            vec![],
            sp(EffectAnnotation::Row(EffectRowAnnotation {
                effects: vec![kea_ast::EffectRowItem {
                    name: "Fail".to_string(),
                    payload: Some("String".to_string()),
                }],
                rest: None,
            })),
            Box::new(TypeAnnotation::Named("Int".to_string())),
        ))),
        default: None,
    };

    let clause = handle_clause(
        "Fail",
        "fail",
        vec![sp(PatternKind::Var("error".to_string()))],
        constructor("Err", vec![var("error")]),
    );
    let then_clause = lambda(&["value"], constructor("Ok", vec![var("value")]));
    let body = handle_expr(call(var("f"), vec![]), vec![clause], Some(then_clause));
    let outer = sp(ExprKind::Lambda {
        params: vec![param],
        body: Box::new(body),
        return_annotation: None,
    });

    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&outer, &mut env, &mut unifier, &records, &traits, &sums);
    assert!(
        !unifier.errors().iter().any(|d| d
            .message
            .contains("expression cannot fail; catch is unnecessary")),
        "catch over higher-order fail parameter should NOT be rejected, got: {:?}",
        unifier.errors()
    );
    // The outer function should infer as fn(fn() -[Fail String]> Int) -> Result(Int, String)
    match &ty {
        Type::Function(ft) => {
            assert!(
                matches!(*ft.ret, Type::Result(_, _)),
                "expected return type to be Result, got {:?}",
                ft.ret
            );
        }
        other => panic!("expected function type, got {other:?}"),
    }
}

#[test]
fn fail_operation_with_never_return_type_acts_as_bottom_in_branches() {
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let fail_effect = make_effect_decl(
        "Fail",
        vec!["E"],
        vec![make_effect_operation(
            "fail",
            vec![annotated_param(
                "error",
                TypeAnnotation::Named("E".to_string()),
            )],
            TypeAnnotation::Named("Never".to_string()),
        )],
    );
    let diags = register_effect_decl(&fail_effect, &records, Some(&sums), &mut env);
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");

    let expr = if_expr(
        lit_bool(true),
        lit_int(7),
        Some(call(
            field_access(var("Fail"), "fail"),
            vec![lit_str("boom")],
        )),
    );
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);
    assert_eq!(ty, Type::Int);
    assert!(
        !unifier.has_errors(),
        "never-return fail branch should typecheck as bottom, got {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_fn_decl_effects_uses_volatile_callback_param_annotation() {
    let env = TypeEnv::new();
    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("apply".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: Some(sp(TypeAnnotation::FunctionWithEffect(
                vec![TypeAnnotation::Named("Int".to_string())],
                sp(effect_row_annotation(vec![("Volatile", None)], None)),
                Box::new(TypeAnnotation::Named("Int".to_string())),
            ))),
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: call(var("f"), vec![lit_int(1)]),
        span: s(),
        where_clause: vec![],
        testing: None,
        testing_tags: Vec::new(),
    };
    let effects = infer_fn_decl_effects(&fn_decl, &env);
    assert_eq!(effects, Effects::pure_volatile());
}

#[test]
fn infer_fn_decl_effects_defaults_effect_var_callback_to_impure() {
    let env = TypeEnv::new();
    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("apply".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: Some(sp(TypeAnnotation::FunctionWithEffect(
                vec![TypeAnnotation::Named("Int".to_string())],
                sp(EffectAnnotation::Var("e".to_string())),
                Box::new(TypeAnnotation::Named("Int".to_string())),
            ))),
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: call(var("f"), vec![lit_int(1)]),
        span: s(),
        where_clause: vec![],
        testing: None,
        testing_tags: Vec::new(),
    };
    let effects = infer_fn_decl_effects(&fn_decl, &env);
    assert_eq!(effects, Effects::impure());
}

#[test]
fn infer_fn_decl_effects_defaults_unsolved_called_term_to_impure() {
    let mut env = TypeEnv::new();
    env.set_function_effect_row("poly_fn".to_string(), EffectRow::open(vec![], RowVarId(77)));
    let fn_decl = make_fn_decl("wrapper", vec![], call(var("poly_fn"), vec![]));
    let effects = infer_fn_decl_effects(&fn_decl, &env);
    assert_eq!(effects, Effects::impure());
}

#[test]
fn infer_fn_decl_effects_propagate_nested_callback_constraints_for_pure_argument() {
    let env = TypeEnv::new();
    let callback_ann = TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    );
    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("drive".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("g".to_string())),
            annotation: Some(sp(TypeAnnotation::FunctionWithEffect(
                vec![callback_ann],
                sp(EffectAnnotation::Var("e".to_string())),
                Box::new(TypeAnnotation::Named("Int".to_string())),
            ))),
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: call(var("g"), vec![lambda(&["x"], var("x"))]),
        span: s(),
        where_clause: vec![],
        testing: None,
        testing_tags: Vec::new(),
    };

    let effects = infer_fn_decl_effects(&fn_decl, &env);
    assert_eq!(effects, Effects::pure_deterministic());
}

#[test]
fn infer_fn_decl_effects_propagate_nested_callback_constraints_for_impure_argument() {
    let env = TypeEnv::new();
    let callback_ann = TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    );
    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("drive".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("g".to_string())),
            annotation: Some(sp(TypeAnnotation::FunctionWithEffect(
                vec![callback_ann],
                sp(EffectAnnotation::Var("e".to_string())),
                Box::new(TypeAnnotation::Named("Int".to_string())),
            ))),
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: call(
            var("g"),
            vec![lambda(
                &["x"],
                block(vec![spawn_expr(lit_int(1)), var("x")]),
            )],
        ),
        span: s(),
        where_clause: vec![],
        testing: None,
        testing_tags: Vec::new(),
    };

    let effects = infer_fn_decl_effects(&fn_decl, &env);
    assert_eq!(effects, Effects::impure());
}

#[test]
fn infer_expr_effects_uses_registered_function_effect_signature_for_callback_polymorphism() {
    let mut env = TypeEnv::new();
    let mut apply = make_fn_decl("apply", vec!["f"], call(var("f"), vec![lit_int(1)]));
    apply.params[0].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    apply.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    register_fn_effect_signature(&apply, &mut env);

    env.set_function_effect_row("pure_cb".to_string(), EffectRow::pure());
    let pure_call = call(var("apply"), vec![var("pure_cb")]);
    assert_eq!(
        infer_expr_effects(&pure_call, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_row(
        "impure_cb".to_string(),
        EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
    );
    let impure_call = call(var("apply"), vec![var("impure_cb")]);
    assert_eq!(infer_expr_effects(&impure_call, &env), Effects::impure());
}

#[test]
fn infer_expr_effects_uses_registered_signature_for_qualified_calls() {
    let mut env = TypeEnv::new();
    env.register_module_function("Kea.List", "apply");
    let mut apply = make_fn_decl("list_apply", vec!["f"], call(var("f"), vec![lit_int(1)]));
    apply.params[0].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    apply.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    register_fn_effect_signature(&apply, &mut env);

    env.set_function_effect_row("pure_cb".to_string(), EffectRow::pure());
    let pure_call = call(field_access(var("List"), "apply"), vec![var("pure_cb")]);
    assert_eq!(
        infer_expr_effects(&pure_call, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_row(
        "impure_cb".to_string(),
        EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
    );
    let impure_call = call(field_access(var("List"), "apply"), vec![var("impure_cb")]);
    assert_eq!(infer_expr_effects(&impure_call, &env), Effects::impure());
}

#[test]
fn infer_expr_effects_uses_registered_signature_for_qualified_callback_arguments() {
    let mut env = TypeEnv::new();
    env.register_module_function("Kea.List", "pure_cb");

    let mut apply = make_fn_decl("apply", vec!["f"], call(var("f"), vec![lit_int(1)]));
    apply.params[0].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    apply.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    register_fn_effect_signature(&apply, &mut env);

    let mut pure_cb = make_fn_decl("list_pure_cb", vec![], lit_int(1));
    pure_cb.effect_annotation = Some(sp(EffectAnnotation::Pure));
    register_fn_effect_signature(&pure_cb, &mut env);

    let expr = call(var("apply"), vec![field_access(var("List"), "pure_cb")]);
    assert_eq!(
        infer_expr_effects(&expr, &env),
        Effects::pure_deterministic()
    );
}

#[test]
fn infer_expr_effects_left_arg_application_call_propagates_callback_effect_signature() {
    let mut env = TypeEnv::new();
    let mut map = make_fn_decl("map", vec!["xs", "f"], call(var("f"), vec![lit_int(1)]));
    map.params[1].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    map.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    register_fn_effect_signature(&map, &mut env);

    env.set_function_effect_row("pure_cb".to_string(), EffectRow::pure());
    let pure_apply = apply_first_arg(
        list(vec![lit_int(1)]),
        call(var("map"), vec![var("pure_cb")]),
    );
    assert_eq!(
        infer_expr_effects(&pure_apply, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_row(
        "impure_cb".to_string(),
        EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
    );
    let impure_apply = apply_first_arg(
        list(vec![lit_int(1)]),
        call(var("map"), vec![var("impure_cb")]),
    );
    assert_eq!(infer_expr_effects(&impure_apply, &env), Effects::impure());
}

#[test]
fn infer_expr_effects_left_arg_application_qualified_call_propagates_callback_effect_signature() {
    let mut env = TypeEnv::new();
    env.register_module_function("Kea.List", "map");
    let mut map = make_fn_decl(
        "list_map",
        vec!["xs", "f"],
        call(var("f"), vec![lit_int(1)]),
    );
    map.params[1].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    map.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    register_fn_effect_signature(&map, &mut env);

    env.set_function_effect_row("pure_cb".to_string(), EffectRow::pure());
    let pure_apply = apply_first_arg(
        list(vec![lit_int(1)]),
        call(field_access(var("List"), "map"), vec![var("pure_cb")]),
    );
    assert_eq!(
        infer_expr_effects(&pure_apply, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_row(
        "impure_cb".to_string(),
        EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
    );
    let impure_apply = apply_first_arg(
        list(vec![lit_int(1)]),
        call(field_access(var("List"), "map"), vec![var("impure_cb")]),
    );
    assert_eq!(infer_expr_effects(&impure_apply, &env), Effects::impure());
}

#[test]
fn infer_expr_effects_shared_effect_var_across_multiple_callback_params() {
    let mut env = TypeEnv::new();

    let callback_ann = TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    );
    let mut zip_apply = make_fn_decl("zip_apply", vec!["f", "g"], lit_int(0));
    zip_apply.params[0].annotation = Some(sp(callback_ann.clone()));
    zip_apply.params[1].annotation = Some(sp(callback_ann));
    zip_apply.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    register_fn_effect_signature(&zip_apply, &mut env);

    env.set_function_effect_row("pure_cb".to_string(), EffectRow::pure());
    env.set_function_effect_row(
        "send_cb".to_string(),
        EffectRow::closed(vec![(Label::new("Send"), Type::Unit)]),
    );
    env.set_function_effect_row(
        "impure_cb".to_string(),
        EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
    );

    let pure_call = call(var("zip_apply"), vec![var("pure_cb"), var("pure_cb")]);
    assert_eq!(
        infer_expr_effects(&pure_call, &env),
        Effects::pure_deterministic()
    );

    let send_call = call(var("zip_apply"), vec![var("pure_cb"), var("send_cb")]);
    // Shared `-[e]>` means both callback args must agree on the same effect
    // variable. `pure` + `Send` is unsatisfiable under equality and
    // conservatively falls back to impure.
    assert_eq!(infer_expr_effects(&send_call, &env), Effects::impure());

    let impure_left = call(var("zip_apply"), vec![var("impure_cb"), var("pure_cb")]);
    assert_eq!(infer_expr_effects(&impure_left, &env), Effects::impure());

    let impure_right = call(var("zip_apply"), vec![var("pure_cb"), var("impure_cb")]);
    assert_eq!(infer_expr_effects(&impure_right, &env), Effects::impure());
}

#[test]
fn infer_expr_effects_let_alias_preserves_function_signature_for_callbacks() {
    let mut env = TypeEnv::new();
    let mut apply = make_fn_decl("apply", vec!["f"], call(var("f"), vec![lit_int(1)]));
    apply.params[0].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    apply.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    register_fn_effect_signature(&apply, &mut env);

    env.set_function_effect_row("pure_cb".to_string(), EffectRow::pure());
    let pure_expr = block(vec![
        let_bind("g", var("apply")),
        call(var("g"), vec![var("pure_cb")]),
    ]);
    assert_eq!(
        infer_expr_effects(&pure_expr, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_row(
        "impure_cb".to_string(),
        EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
    );
    let impure_expr = block(vec![
        let_bind("g", var("apply")),
        call(var("g"), vec![var("impure_cb")]),
    ]);
    assert_eq!(infer_expr_effects(&impure_expr, &env), Effects::impure());
}

#[test]
fn infer_expr_effects_let_alias_preserves_qualified_function_signature() {
    let mut env = TypeEnv::new();
    env.register_module_function("Kea.List", "apply");
    let mut apply = make_fn_decl("list_apply", vec!["f"], call(var("f"), vec![lit_int(1)]));
    apply.params[0].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    apply.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    register_fn_effect_signature(&apply, &mut env);

    env.set_function_effect_row("pure_cb".to_string(), EffectRow::pure());
    let expr = block(vec![
        let_bind("g", field_access(var("List"), "apply")),
        call(var("g"), vec![var("pure_cb")]),
    ]);
    assert_eq!(
        infer_expr_effects(&expr, &env),
        Effects::pure_deterministic()
    );
}

#[test]
fn infer_expr_effects_let_alias_lambda_uses_body_effect() {
    let env = TypeEnv::new();
    let expr = block(vec![
        let_bind("run", lambda(&[], spawn_expr(lit_int(1)))),
        call(var("run"), vec![]),
    ]);
    assert_eq!(infer_expr_effects(&expr, &env), Effects::impure());
}

#[test]
fn infer_expr_effects_let_alias_lambda_preserves_callback_effect_constraints() {
    let mut env = TypeEnv::new();
    let apply_lambda = sp(ExprKind::Lambda {
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: Some(sp(TypeAnnotation::FunctionWithEffect(
                vec![TypeAnnotation::Named("Int".to_string())],
                sp(EffectAnnotation::Var("e".to_string())),
                Box::new(TypeAnnotation::Named("Int".to_string())),
            ))),
            default: None,
        }],
        body: Box::new(call(var("f"), vec![lit_int(1)])),
        return_annotation: None,
    });

    env.set_function_effect_row("pure_cb".to_string(), EffectRow::pure());
    let pure_expr = block(vec![
        let_bind("apply", apply_lambda.clone()),
        call(var("apply"), vec![var("pure_cb")]),
    ]);
    assert_eq!(
        infer_expr_effects(&pure_expr, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_row(
        "impure_cb".to_string(),
        EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
    );
    let impure_expr = block(vec![
        let_bind("apply", apply_lambda),
        call(var("apply"), vec![var("impure_cb")]),
    ]);
    assert_eq!(infer_expr_effects(&impure_expr, &env), Effects::impure());
}

#[test]
fn infer_expr_effects_let_call_result_preserves_returned_callable_effect_row() {
    let mut env = TypeEnv::new();
    env.bind(
        "make_emitter".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![],
            ret: Box::new(Type::Function(FunctionType {
                params: vec![Type::Int],
                ret: Box::new(Type::Unit),
                effects: EffectRow::closed(vec![(Label::new("Emit"), Type::Unit)]),
            })),
            effects: EffectRow::pure(),
        })),
    );

    let trap = make_fn_decl(
        "trap",
        vec![],
        block(vec![
            let_bind("f", call(var("make_emitter"), vec![])),
            call(var("f"), vec![lit_int(42)]),
        ]),
    );
    let row = infer_fn_decl_effect_row(&trap, &env);
    assert!(
        row.row.has(&Label::new("Emit")),
        "expected returned callable effect row to propagate Emit, got {row:?}"
    );
    assert!(
        !row.row.has(&Label::new("IO")),
        "expected no phantom IO from let-bound call result, got {row:?}"
    );
}

#[test]
fn infer_expr_effects_direct_curried_call_preserves_returned_callable_effect_row() {
    let mut env = TypeEnv::new();
    let emit_fn = Type::Function(FunctionType {
        params: vec![Type::Int],
        ret: Box::new(Type::Unit),
        effects: EffectRow::closed(vec![(Label::new("Emit"), Type::Unit)]),
    });
    env.bind("logger".to_string(), TypeScheme::mono(emit_fn.clone()));
    env.bind(
        "apply".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![emit_fn],
            ret: Box::new(Type::Function(FunctionType {
                params: vec![Type::Int],
                ret: Box::new(Type::Unit),
                effects: EffectRow::closed(vec![(Label::new("Emit"), Type::Unit)]),
            })),
            effects: EffectRow::pure(),
        })),
    );

    let trap = make_fn_decl(
        "trap",
        vec![],
        call(call(var("apply"), vec![var("logger")]), vec![lit_int(42)]),
    );
    let row = infer_fn_decl_effect_row(&trap, &env);
    assert!(
        row.row.has(&Label::new("Emit")),
        "expected direct curried call to preserve Emit, got {row:?}"
    );
    assert!(
        !row.row.has(&Label::new("IO")),
        "expected no phantom IO from direct curried call, got {row:?}"
    );
}

#[test]
fn validate_declared_fn_effect_accepts_weaker_or_equal_inferred_effect() {
    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(effect_row_annotation(vec![("IO", None)], None)));
    let inferred = Effects::pure_deterministic();
    assert!(validate_declared_fn_effect(&fn_decl, inferred).is_ok());
}

#[test]
fn validate_declared_fn_effect_rejects_too_weak_declaration() {
    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(EffectAnnotation::Pure));
    let inferred = Effects::impure();
    let err = validate_declared_fn_effect(&fn_decl, inferred)
        .expect_err("pure declaration should reject impure body");
    assert!(
        err.message.contains("declared effect `pure` is too weak"),
        "unexpected message: {}",
        err.message
    );
}

#[test]
fn validate_declared_fn_effect_rejects_unconstrained_effect_variable() {
    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    let inferred = Effects::pure_deterministic();
    let err = validate_declared_fn_effect(&fn_decl, inferred)
        .expect_err("unconstrained effect variables should be rejected");
    assert!(
        err.message.contains("effect variable `e` is unconstrained"),
        "unexpected message: {}",
        err.message
    );
}

#[test]
fn validate_declared_fn_effect_accepts_closed_row_annotation() {
    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(effect_row_annotation(vec![("IO", None)], None)));
    let inferred = Effects::impure();
    assert!(validate_declared_fn_effect(&fn_decl, inferred).is_ok());
}

#[test]
fn validate_declared_fn_effect_rejects_legacy_impure_contract_annotation() {
    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(EffectAnnotation::Impure));
    let inferred = Effects::impure();
    let err = validate_declared_fn_effect(&fn_decl, inferred)
        .expect_err("legacy impure annotation should not participate in row contracts");
    assert!(
        err.message.contains("invalid effect-row contract"),
        "unexpected message: {}",
        err.message
    );
}

#[test]
fn validate_declared_fn_effect_accepts_open_row_with_concrete_entries() {
    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(effect_row_annotation(vec![("IO", None)], Some("e"))));
    let inferred = Effects::impure();
    assert!(validate_declared_fn_effect(&fn_decl, inferred).is_ok());
}

#[test]
fn effect_row_subsumption_allows_declared_superset() {
    let actual = EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]);
    let declared = EffectRow::closed(vec![
        (Label::new("IO"), Type::Unit),
        (Label::new("Fail"), Type::String),
        (Label::new("Send"), Type::Unit),
    ]);
    assert!(unify_effect_row_subsumption(&actual, &declared, s()).is_ok());
}

#[test]
fn effect_row_subsumption_rejects_inferred_extra_effects() {
    let actual = EffectRow::closed(vec![
        (Label::new("IO"), Type::Unit),
        (Label::new("Fail"), Type::String),
        (Label::new("Send"), Type::Unit),
    ]);
    let declared = EffectRow::closed(vec![
        (Label::new("IO"), Type::Unit),
        (Label::new("Send"), Type::Unit),
    ]);
    let err = unify_effect_row_subsumption(&actual, &declared, s())
        .expect_err("closed declared row should reject inferred extra effects");
    assert!(
        err.message.contains("declared effect row is too weak"),
        "unexpected message: {}",
        err.message
    );
}

#[test]
fn effect_row_subsumption_accepts_open_declared_tail() {
    let actual = EffectRow::closed(vec![
        (Label::new("IO"), Type::Unit),
        (Label::new("Send"), Type::Unit),
        (Label::new("Spawn"), Type::Unit),
    ]);
    let declared = EffectRow::open(
        vec![
            (Label::new("IO"), Type::Unit),
            (Label::new("Send"), Type::Unit),
        ],
        RowVarId(99),
    );
    assert!(unify_effect_row_subsumption(&actual, &declared, s()).is_ok());
}

#[test]
fn validate_declared_fn_effect_rejects_multiple_incompatible_fail_payloads() {
    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(effect_row_annotation(
        vec![("Fail", Some("String")), ("Fail", Some("Int"))],
        None,
    )));
    let inferred = Effects::impure();
    let err = validate_declared_fn_effect(&fn_decl, inferred)
        .expect_err("multiple incompatible Fail payloads should be rejected");
    assert!(
        err.message.contains("multiple incompatible `Fail` entries"),
        "unexpected message: {}",
        err.message
    );
}

#[test]
fn validate_declared_fn_effect_allows_tail_only_row_effect_variable() {
    let env = TypeEnv::new();
    let mut fn_decl = make_fn_decl("f", vec!["g"], call(var("g"), vec![lit_int(1)]));
    fn_decl.params[0].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(effect_row_annotation(vec![], Some("e"))),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    fn_decl.effect_annotation = Some(sp(effect_row_annotation(vec![], Some("e"))));
    let inferred = infer_fn_decl_effects(&fn_decl, &env);
    assert!(validate_declared_fn_effect_with_env(&fn_decl, inferred, &env).is_ok());
}

#[test]
fn validate_declared_fn_effect_allows_constrained_effect_variable() {
    let env = TypeEnv::new();
    let mut fn_decl = make_fn_decl("f", vec!["g"], call(var("g"), vec![lit_int(1)]));
    fn_decl.params[0].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    fn_decl.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    let inferred = infer_fn_decl_effects(&fn_decl, &env);
    assert!(validate_declared_fn_effect_with_env(&fn_decl, inferred, &env).is_ok());
}

#[test]
fn validate_declared_fn_effect_rejects_non_propagating_effect_variable_contract() {
    let env = TypeEnv::new();
    let mut fn_decl = make_fn_decl(
        "f",
        vec!["g"],
        block(vec![spawn_expr(lit_int(1)), lit_int(1)]),
    );
    fn_decl.params[0].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    fn_decl.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));

    let inferred = infer_fn_decl_effects(&fn_decl, &env);
    let err = validate_declared_fn_effect_with_env(&fn_decl, inferred, &env)
        .expect_err("effect variable contract should fail when body is always impure");
    assert!(
        err.message
            .contains("declared effect `-[e]>` on `f` does not match body effect propagation"),
        "unexpected message: {}",
        err.message
    );
}

#[test]
fn validate_trait_method_impl_effect_rejects_stronger_impl_effect() {
    let err = validate_trait_method_impl_effect(
        "Runner",
        "run",
        s(),
        Effects::impure(),
        Effects::pure_deterministic(),
    )
    .expect_err("impure impl should violate pure trait contract");
    assert!(
        err.message.contains("trait `Runner` requires `[]`"),
        "unexpected message: {}",
        err.message
    );
}

#[test]
fn validate_trait_method_impl_contract_rejects_missing_polymorphic_impl_annotation() {
    let err = validate_trait_method_impl_contract(
        "Runner",
        "run",
        s(),
        Effects::pure_deterministic(),
        None,
        &[],
        Some(&EffectAnnotation::Var("e".to_string())),
    )
    .expect_err("missing impl effect variable should violate polymorphic trait contract");
    assert!(
        err.message.contains(
            "must declare an effect variable (`-[e]>`) to satisfy polymorphic trait method contract"
        ),
        "unexpected message: {}",
        err.message
    );
}

#[test]
fn validate_trait_method_impl_contract_accepts_constrained_polymorphic_impl_annotation() {
    let impl_effect = sp(EffectAnnotation::Var("impl_e".to_string()));
    let params = vec![Param {
        label: ParamLabel::Implicit,
        pattern: sp(PatternKind::Var("f".to_string())),
        annotation: Some(sp(TypeAnnotation::FunctionWithEffect(
            vec![TypeAnnotation::Named("Int".to_string())],
            sp(EffectAnnotation::Var("impl_e".to_string())),
            Box::new(TypeAnnotation::Named("Int".to_string())),
        ))),
        default: None,
    }];
    assert!(
        validate_trait_method_impl_contract(
            "Runner",
            "run",
            s(),
            Effects::pure_deterministic(),
            Some(&impl_effect),
            &params,
            Some(&EffectAnnotation::Var("e".to_string())),
        )
        .is_ok()
    );
}

#[test]
fn validate_trait_method_impl_contract_with_env_accepts_exact_polymorphic_propagation() {
    let env = TypeEnv::new();
    let mut method = make_fn_decl("run", vec!["f"], call(var("f"), vec![lit_int(1)]));
    method.params[0].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("impl_e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    method.effect_annotation = Some(sp(EffectAnnotation::Var("impl_e".to_string())));

    let inferred = infer_fn_decl_effects(&method, &env);
    assert!(
        validate_trait_method_impl_contract_with_env(
            "Runner",
            &method,
            inferred,
            &env,
            Some(&EffectAnnotation::Var("e".to_string())),
        )
        .is_ok()
    );
}

#[test]
fn validate_trait_method_impl_contract_with_env_rejects_non_propagating_polymorphic_impl() {
    let env = TypeEnv::new();
    let mut method = make_fn_decl(
        "run",
        vec!["f"],
        block(vec![spawn_expr(lit_int(1)), lit_int(1)]),
    );
    method.params[0].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("impl_e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    method.effect_annotation = Some(sp(EffectAnnotation::Var("impl_e".to_string())));

    let inferred = infer_fn_decl_effects(&method, &env);
    let err = validate_trait_method_impl_contract_with_env(
        "Runner",
        &method,
        inferred,
        &env,
        Some(&EffectAnnotation::Var("e".to_string())),
    )
    .expect_err("non-propagating polymorphic impl should be rejected");
    assert!(
        err.message.contains(
            "declared effect `-[impl_e]>` on `run` does not match body effect propagation"
        ),
        "unexpected message: {}",
        err.message
    );
}

#[test]
fn trait_method_effect_variable_requires_constraint() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let mut method = make_trait_method(
        "run",
        vec![("self", None)],
        Some(TypeAnnotation::Named("Int".to_string())),
    );
    method.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    let def = make_trait_def("Runner", vec![method]);
    let err = traits
        .register_trait(&def, &records)
        .expect_err("trait methods should reject unconstrained effect variables");
    assert!(
        err.message
            .contains("effect variable `e` is unconstrained in trait method"),
        "unexpected message: {}",
        err.message
    );
}

#[test]
fn trait_method_effect_variable_is_allowed_when_constrained() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let mut method = make_trait_method(
        "run",
        vec![
            ("self", None),
            (
                "f",
                Some(TypeAnnotation::FunctionWithEffect(
                    vec![TypeAnnotation::Named("Int".to_string())],
                    sp(EffectAnnotation::Var("e".to_string())),
                    Box::new(TypeAnnotation::Named("Int".to_string())),
                )),
            ),
        ],
        Some(TypeAnnotation::Named("Int".to_string())),
    );
    method.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    let def = make_trait_def("Runner", vec![method]);
    traits
        .register_trait(&def, &records)
        .expect("trait methods should allow constrained effect variables");
    let info = traits.lookup_trait("Runner").expect("Runner should exist");
    assert_eq!(
        info.methods[0].declared_effect,
        Some(EffectAnnotation::Var("e".to_string()))
    );
}

#[test]
fn trait_method_allows_rank2_forall_parameter_annotation() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let method = make_trait_method(
        "apply",
        vec![(
            "f",
            Some(TypeAnnotation::Forall {
                type_vars: vec!["a".to_string()],
                ty: Box::new(TypeAnnotation::Function(
                    vec![TypeAnnotation::Named("a".to_string())],
                    Box::new(TypeAnnotation::Named("a".to_string())),
                )),
            }),
        )],
        Some(TypeAnnotation::Named("Int".to_string())),
    );
    let def = make_trait_def("Rank2Applier", vec![method]);
    traits
        .register_trait(&def, &records)
        .expect("trait registration should accept rank-2 method parameter annotations");
    let info = traits
        .lookup_trait("Rank2Applier")
        .expect("Rank2Applier should exist");
    assert!(
        matches!(info.methods[0].param_types[0], Type::Forall(_)),
        "expected method parameter type to retain rank-2 forall"
    );
}

#[test]
fn trait_registration_stores_trait_method_effect_contract() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let mut method = make_trait_method(
        "run",
        vec![("self", None)],
        Some(TypeAnnotation::Named("Int".to_string())),
    );
    method.effect_annotation = Some(sp(EffectAnnotation::Pure));
    let def = make_trait_def("Runner", vec![method]);
    traits
        .register_trait(&def, &records)
        .expect("trait registration should succeed");
    let info = traits.lookup_trait("Runner").expect("Runner should exist");
    assert_eq!(
        info.methods[0].declared_effect,
        Some(EffectAnnotation::Pure)
    );
}

#[test]
fn trait_register_and_lookup() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = make_trait_def(
        "Show",
        vec![make_trait_method(
            "show",
            vec![("self", None)],
            Some(TypeAnnotation::Named("String".into())),
        )],
    );
    traits.register_trait(&def, &records).unwrap();
    let info = traits
        .lookup_trait("Show")
        .expect("Show should be registered");
    assert_eq!(info.name, "Show");
    assert_eq!(info.methods.len(), 1);
    assert_eq!(info.methods[0].name, "show");
    assert_eq!(info.methods[0].return_type, Type::String);
}

#[test]
fn trait_registers_supertraits() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Eq", vec![]), &records)
        .unwrap();
    let orderable = kea_ast::TraitDef {
        public: false,
        name: sp("Orderable".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![sp("Eq".to_string())],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&orderable, &records).unwrap();
    let info = traits
        .lookup_trait("Orderable")
        .expect("Orderable should exist");
    assert_eq!(info.supertraits, vec!["Eq".to_string()]);
}

#[test]
fn trait_unknown_supertrait_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Orderable".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![sp("Eq".to_string())],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    let result = traits.register_trait(&def, &records);
    assert!(result.is_err());
    assert!(
        result
            .unwrap_err()
            .message
            .contains("unknown supertrait `Eq`"),
    );
}

#[test]
fn trait_duplicate_supertrait_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Eq", vec![]), &records)
        .unwrap();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Orderable".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![sp("Eq".to_string()), sp("Eq".to_string())],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    let result = traits.register_trait(&def, &records);
    assert!(result.is_err());
    assert!(
        result
            .unwrap_err()
            .message
            .contains("duplicate supertrait `Eq`")
    );
}

#[test]
fn trait_self_supertrait_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Eq".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![sp("Eq".to_string())],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    let result = traits.register_trait(&def, &records);
    assert!(result.is_err());
    assert!(
        result
            .unwrap_err()
            .message
            .contains("cannot inherit from itself")
    );
}

#[test]
fn trait_duplicate_definition_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = make_trait_def("Show", vec![]);
    traits.register_trait(&def, &records).unwrap();
    let result = traits.register_trait(&def, &records);
    assert!(result.is_err());
    assert!(result.unwrap_err().message.contains("already defined"));
}

#[test]
fn trait_names_lists_registered() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();
    traits
        .register_trait(&make_trait_def("Eq", vec![]), &records)
        .unwrap();
    let names: Vec<&str> = traits.trait_names().collect();
    assert_eq!(names, vec!["Eq", "Show"]); // BTreeMap is sorted
}

#[test]
fn trait_impl_registers_successfully() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(
            &make_trait_def(
                "Show",
                vec![make_trait_method(
                    "show",
                    vec![("self", None)],
                    Some(TypeAnnotation::Named("String".into())),
                )],
            ),
            &records,
        )
        .unwrap();

    let impl_block = make_impl_block(
        "Show",
        "Int",
        vec![make_fn_decl("show", vec!["self"], lit_str("int"))],
    );
    traits.register_trait_impl(&impl_block).unwrap();
    assert!(has_unique_impl(&traits, "Show", Type::Int));
}

#[test]
fn trait_impl_accepts_concrete_self_when_hkts_disabled() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let bind_trait = kea_ast::TraitDef {
        public: false,
        name: sp("Bind".to_string()),
        doc: None,
        type_params: vec![TraitTypeParam {
            name: sp("F".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&bind_trait, &records).unwrap();

    traits
        .register_trait_impl(&make_impl_block("Bind", "Int", vec![]))
        .expect("Kea v0 disables HKT kind arrows, so concrete Self types are accepted");
}

#[test]
fn trait_impl_kind_partial_application_accepts_result_hole() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let bind_trait = kea_ast::TraitDef {
        public: false,
        name: sp("Bind".to_string()),
        doc: None,
        type_params: vec![TraitTypeParam {
            name: sp("F".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&bind_trait, &records).unwrap();

    let impl_block = make_impl_block_with_params("Bind", "Result", vec!["_", "e"], vec![], vec![]);
    traits.register_trait_impl(&impl_block).unwrap();
}

#[test]
fn trait_impl_named_self_param_is_not_kind_restricted_in_v0() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: false,
        name: sp("NamedSelf".to_string()),
        doc: None,
        type_params: vec![
            TraitTypeParam {
                name: sp("X".to_string()),
                kind: kind_star(),
            },
            TraitTypeParam {
                name: sp("Self".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&trait_def, &records).unwrap();

    // Kea v0 has no HKT kind arrows; both List and Int are accepted here.
    traits
        .register_trait_impl(&make_impl_block("NamedSelf", "List", vec![]))
        .expect("List should satisfy named Self kind");
    traits
        .register_trait_impl(&make_impl_block("NamedSelf", "Int", vec![]))
        .expect("Int is also accepted when HKT kind arrows are disabled");
}

#[test]
fn trait_impl_accepts_trait_with_multiple_type_params_when_self_kind_matches() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: false,
        name: sp("BiLike".to_string()),
        doc: None,
        type_params: vec![
            TraitTypeParam {
                name: sp("F".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
            TraitTypeParam {
                name: sp("G".to_string()),
                kind: kind_star(),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&trait_def, &records).unwrap();

    let impl_block = make_impl_block("BiLike", "List", vec![]);
    traits.register_trait_impl(&impl_block).unwrap();
}

#[test]
fn trait_impl_accepts_first_trait_param_when_hkts_disabled() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: false,
        name: sp("BiLike".to_string()),
        doc: None,
        type_params: vec![
            TraitTypeParam {
                name: sp("F".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
            TraitTypeParam {
                name: sp("G".to_string()),
                kind: kind_star(),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&trait_def, &records).unwrap();

    traits
        .register_trait_impl(&make_impl_block("BiLike", "Int", vec![]))
        .expect("Kea v0 disables HKT kind arrows, so concrete Self types are accepted");
}

#[test]
fn trait_parametric_impl_satisfies_recursive_bounds() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();

    traits
        .register_trait_impl(&make_impl_block("Show", "Int", vec![]))
        .unwrap();

    let list_impl = make_impl_block_with_params(
        "Show",
        "List",
        vec!["t"],
        vec![kea_ast::WhereItem::TraitBound(kea_ast::TraitBound {
            type_var: sp("t".to_string()),
            trait_name: sp("Show".to_string()),
        })],
        vec![],
    );
    traits.register_trait_impl(&list_impl).unwrap();

    assert!(has_unique_impl(
        &traits,
        "Show",
        Type::List(Box::new(Type::Int))
    ));
    assert!(!has_unique_impl(
        &traits,
        "Show",
        Type::List(Box::new(Type::Float))
    ));
}

#[test]
fn trait_satisfies_requires_supertrait_impls() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Eq", vec![]), &records)
        .unwrap();
    let orderable = kea_ast::TraitDef {
        public: false,
        name: sp("Orderable".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![sp("Eq".to_string())],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&orderable, &records).unwrap();

    let orderable_int = make_impl_block("Orderable", "Int", vec![]);
    traits.register_trait_impl(&orderable_int).unwrap();

    assert!(
        !has_unique_impl(&traits, "Orderable", Type::Int),
        "Orderable should be unsatisfied when Eq impl is missing"
    );

    let eq_int = make_impl_block("Eq", "Int", vec![]);
    traits.register_trait_impl(&eq_int).unwrap();
    assert!(has_unique_impl(&traits, "Orderable", Type::Int));
    assert_eq!(
        traits.trait_closure("Orderable"),
        vec!["Orderable".to_string(), "Eq".to_string()]
    );
}

#[test]
fn trait_impl_unknown_trait_errors() {
    let mut traits = TraitRegistry::new();
    let impl_block = make_impl_block("Unknown", "Int", vec![]);
    let result = traits.register_trait_impl(&impl_block);
    assert!(result.is_err());
    assert!(result.unwrap_err().message.contains("not defined"));
}

#[test]
fn trait_impl_duplicate_coherence_error() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();

    let impl_block = make_impl_block("Show", "Int", vec![]);
    traits.register_trait_impl(&impl_block).unwrap();

    // Second impl of Show for Int → coherence error
    let impl_block2 = make_impl_block("Show", "Int", vec![]);
    let result = traits.register_trait_impl(&impl_block2);
    assert!(result.is_err());
    assert!(result.unwrap_err().message.contains("already implemented"));
}

#[test]
fn trait_impl_rejects_mixed_bare_and_parametric() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();

    traits
        .register_trait_impl(&make_impl_block("Show", "List", vec![]))
        .unwrap();

    let parametric = make_impl_block_with_params("Show", "List", vec!["t"], vec![], vec![]);
    let err = traits.register_trait_impl(&parametric).unwrap_err();
    assert!(err.message.contains("cannot mix bare and parametric impls"));
}

#[test]
fn trait_impl_rejects_overlapping_parametric_impls() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();
    traits
        .register_trait(&make_trait_def("Eq", vec![]), &records)
        .unwrap();

    let impl_a = make_impl_block_with_params(
        "Show",
        "List",
        vec!["t"],
        vec![kea_ast::WhereItem::TraitBound(kea_ast::TraitBound {
            type_var: sp("t".to_string()),
            trait_name: sp("Show".to_string()),
        })],
        vec![],
    );
    let impl_b = make_impl_block_with_params(
        "Show",
        "List",
        vec!["u"],
        vec![kea_ast::WhereItem::TraitBound(kea_ast::TraitBound {
            type_var: sp("u".to_string()),
            trait_name: sp("Eq".to_string()),
        })],
        vec![],
    );

    traits.register_trait_impl(&impl_a).unwrap();
    let err = traits.register_trait_impl(&impl_b).unwrap_err();
    assert!(err.message.contains("conflicting implementation"));
}

#[test]
fn sendable_parametric_dispatch_handles_nested_and_non_sendable_cases() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Sendable", vec![]), &records)
        .unwrap();

    for ty in ["Int", "String"] {
        traits
            .register_trait_impl(&make_impl_block("Sendable", ty, vec![]))
            .unwrap();
    }
    traits
        .register_trait_impl(&make_impl_block_with_params(
            "Sendable",
            "List",
            vec!["t"],
            vec![kea_ast::WhereItem::TraitBound(kea_ast::TraitBound {
                type_var: sp("t".to_string()),
                trait_name: sp("Sendable".to_string()),
            })],
            vec![],
        ))
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block_with_params(
            "Sendable",
            "Map",
            vec!["k", "v"],
            vec![
                kea_ast::WhereItem::TraitBound(kea_ast::TraitBound {
                    type_var: sp("k".to_string()),
                    trait_name: sp("Sendable".to_string()),
                }),
                kea_ast::WhereItem::TraitBound(kea_ast::TraitBound {
                    type_var: sp("v".to_string()),
                    trait_name: sp("Sendable".to_string()),
                }),
            ],
            vec![],
        ))
        .unwrap();

    assert!(has_unique_impl(
        &traits,
        "Sendable",
        Type::List(Box::new(Type::Int))
    ));
    assert!(has_unique_impl(
        &traits,
        "Sendable",
        Type::List(Box::new(Type::List(Box::new(Type::String))))
    ));
    assert!(has_unique_impl(
        &traits,
        "Sendable",
        Type::Map(
            Box::new(Type::String),
            Box::new(Type::List(Box::new(Type::Int))),
        )
    ));

    let fn_ty = Type::Function(FunctionType {
        params: vec![Type::Int],
        ret: Box::new(Type::Int),
        effects: EffectRow::pure(),
    });
    assert!(!has_unique_impl(
        &traits,
        "Sendable",
        Type::List(Box::new(fn_ty))
    ));
}

#[test]
fn trait_impl_different_types_ok() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();

    traits
        .register_trait_impl(&make_impl_block("Show", "Int", vec![]))
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block("Show", "String", vec![]))
        .unwrap();

    assert!(has_unique_impl(&traits, "Show", Type::Int));
    assert!(has_unique_impl(&traits, "Show", Type::String));
    assert!(!has_unique_impl(&traits, "Show", Type::Float));
}

#[test]
fn orphan_rule_rejects_foreign_trait_for_foreign_builtin_type() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let show_def = make_trait_def("Show", vec![]);
    traits
        .register_trait_with_owner(&show_def, &records, "pkg:alpha")
        .unwrap();

    let impl_block = make_impl_block("Show", "Int", vec![]);
    let result = traits.register_trait_impl_in_module(&impl_block, "pkg:beta");
    assert!(result.is_err());
    let msg = result.unwrap_err().message;
    assert!(msg.contains("orphan rule"));
}

#[test]
fn orphan_rule_allows_foreign_trait_for_local_type() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let show_def = make_trait_def("Show", vec![]);
    traits
        .register_trait_with_owner(&show_def, &records, "pkg:alpha")
        .unwrap();
    traits.register_type_owner("MyType", "pkg:beta");

    let impl_block = make_impl_block("Show", "MyType", vec![]);
    let result = traits.register_trait_impl_in_module(&impl_block, "pkg:beta");
    assert!(result.is_ok());
}

// --- Per-package orphan rule scope tests ---

#[test]
fn ownership_scope_same_package() {
    assert!(same_ownership_scope("pkg:my_lib", "pkg:my_lib"));
}

#[test]
fn ownership_scope_different_packages() {
    assert!(!same_ownership_scope("pkg:my_lib", "pkg:other"));
}

#[test]
fn ownership_scope_same_project() {
    assert!(same_ownership_scope("project:Foo", "project:Foo.Bar"));
}

#[test]
fn ownership_scope_package_vs_project() {
    assert!(!same_ownership_scope("pkg:my_lib", "project:Foo"));
}

#[test]
fn ownership_scope_kea_builtin() {
    assert!(same_ownership_scope("kea:", "kea:"));
}

#[test]
fn ownership_scope_repl() {
    assert!(same_ownership_scope("repl:", "repl:"));
}

#[test]
fn ownership_scope_cross_scope() {
    assert!(!same_ownership_scope("kea:", "repl:"));
    assert!(!same_ownership_scope("repl:", "project:Foo"));
    assert!(!same_ownership_scope("kea:", "pkg:my_lib"));
}

#[test]
#[should_panic(expected = "owner tags must be tagged")]
fn register_type_owner_rejects_untagged_owner() {
    let mut traits = TraitRegistry::new();
    traits.register_type_owner("Widget", "SomeModule");
}

#[test]
fn orphan_rule_allows_same_package_impl() {
    // A type defined in package "my_lib" can have impls added from the same package
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let show_def = make_trait_def("Show", vec![]);
    traits
        .register_trait_with_owner(&show_def, &records, "pkg:my_lib")
        .unwrap();
    traits.register_type_owner("Widget", "pkg:my_lib");

    let impl_block = make_impl_block("Show", "Widget", vec![]);
    // Same package scope — should succeed
    let result = traits.register_trait_impl_in_module(&impl_block, "pkg:my_lib");
    assert!(result.is_ok());
}

#[test]
fn orphan_rule_rejects_cross_package_impl() {
    // A type in package "alpha" cannot have impls from package "beta"
    // when the trait is also from "alpha"
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let show_def = make_trait_def("Show", vec![]);
    traits
        .register_trait_with_owner(&show_def, &records, "pkg:alpha")
        .unwrap();
    traits.register_type_owner("Widget", "pkg:alpha");

    let impl_block = make_impl_block("Show", "Widget", vec![]);
    let result = traits.register_trait_impl_in_module(&impl_block, "pkg:beta");
    assert!(result.is_err());
    assert!(result.unwrap_err().message.contains("orphan rule"));
}

#[test]
fn orphan_rule_allows_project_impl_for_project_type() {
    // All project modules share one scope
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let show_def = make_trait_def("Show", vec![]);
    traits
        .register_trait_with_owner(&show_def, &records, "project:MyApp")
        .unwrap();
    traits.register_type_owner("Widget", "project:MyApp.Models");

    let impl_block = make_impl_block("Show", "Widget", vec![]);
    // Different project modules but same project scope — should succeed
    let result = traits.register_trait_impl_in_module(&impl_block, "project:MyApp.Views");
    assert!(result.is_ok());
}

#[test]
fn trait_satisfies_returns_false_for_unregistered() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();
    assert!(!has_unique_impl(&traits, "Show", Type::Int));
    assert!(!has_unique_impl(&traits, "NonExistent", Type::Int));
}

#[test]
fn trait_add_impl_methods() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(
            &make_trait_def(
                "Show",
                vec![make_trait_method(
                    "show",
                    vec![("self", None)],
                    Some(TypeAnnotation::Named("String".into())),
                )],
            ),
            &records,
        )
        .unwrap();

    traits
        .register_trait_impl(&make_impl_block("Show", "Int", vec![]))
        .unwrap();

    // Simulate adding resolved method types
    let mut methods = BTreeMap::new();
    let fn_type = Type::Function(FunctionType {
        params: vec![Type::Int],
        ret: Box::new(Type::String),
        effects: EffectRow::pure(),
    });
    methods.insert("show".to_string(), fn_type.clone());
    traits.add_impl_methods(methods).unwrap();

    let found = traits
        .lookup_trait_method_for_type("Int", "show")
        .expect("lookup should not be ambiguous")
        .expect("method should exist");
    assert_eq!(found.0, "Show");
    assert_eq!(found.1, fn_type);
}

#[test]
fn trait_lookup_method_for_type_unique() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(
            &make_trait_def(
                "Show",
                vec![make_trait_method(
                    "show",
                    vec![("self", None)],
                    Some(TypeAnnotation::Named("String".into())),
                )],
            ),
            &records,
        )
        .unwrap();
    traits.register_type_owner("Point", "repl:");
    traits
        .register_trait_impl(&make_impl_block("Show", "Point", vec![]))
        .unwrap();
    let mut methods = BTreeMap::new();
    methods.insert(
        "show".to_string(),
        Type::Function(FunctionType {
            params: vec![Type::Record(RecordType {
                name: "Point".to_string(),
                params: vec![],
                row: RowType::closed(vec![]),
            })],
            ret: Box::new(Type::String),
            effects: EffectRow::pure(),
        }),
    );
    traits.add_impl_methods(methods).unwrap();

    let found = traits.lookup_trait_method_for_type("Point", "show");
    assert!(matches!(found, Ok(Some(("Show", _)))));
}

#[test]
fn trait_lookup_method_for_type_ambiguous() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    for trait_name in ["Show", "Debug"] {
        traits
            .register_trait(
                &make_trait_def(
                    trait_name,
                    vec![make_trait_method(
                        "render",
                        vec![("self", None)],
                        Some(TypeAnnotation::Named("String".into())),
                    )],
                ),
                &records,
            )
            .unwrap();
    }
    traits.register_type_owner("Point", "repl:");

    for trait_name in ["Show", "Debug"] {
        traits
            .register_trait_impl(&make_impl_block(trait_name, "Point", vec![]))
            .unwrap();
        let mut methods = BTreeMap::new();
        methods.insert(
            "render".to_string(),
            Type::Function(FunctionType {
                params: vec![Type::Record(RecordType {
                    name: "Point".to_string(),
                    params: vec![],
                    row: RowType::closed(vec![]),
                })],
                ret: Box::new(Type::String),
                effects: EffectRow::pure(),
            }),
        );
        traits.add_impl_methods(methods).unwrap();
    }

    let found = traits.lookup_trait_method_for_type("Point", "render");
    assert!(matches!(found, Err(candidates) if candidates.len() == 2));
}

#[test]
fn trait_find_impl_not_found() {
    let traits = TraitRegistry::new();
    let outcome = traits.solve_goal(&TraitGoal::Implements {
        trait_name: "Show".to_string(),
        ty: Type::Int,
    });
    assert!(matches!(outcome, SolveOutcome::NoMatch(_)));
}

#[test]
fn trait_method_with_annotated_params() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = make_trait_def(
        "Additive",
        vec![make_trait_method(
            "add",
            vec![
                ("self", None),
                ("other", Some(TypeAnnotation::Named("Int".into()))),
            ],
            Some(TypeAnnotation::Named("Int".into())),
        )],
    );
    traits.register_trait(&def, &records).unwrap();
    let info = traits.lookup_trait("Additive").unwrap();
    assert_eq!(info.methods[0].param_types.len(), 2);
    // self → placeholder type var
    assert_eq!(
        info.methods[0].param_types[0],
        Type::Var(TypeVarId(u32::MAX))
    );
    // other → Int (resolved from annotation)
    assert_eq!(info.methods[0].param_types[1], Type::Int);
    assert_eq!(info.methods[0].return_type, Type::Int);
}

#[test]
fn trait_method_unknown_param_type_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = make_trait_def(
        "Bad",
        vec![make_trait_method(
            "bad_method",
            vec![("x", Some(TypeAnnotation::Named("Nonexistent".into())))],
            None,
        )],
    );
    let result = traits.register_trait(&def, &records);
    assert!(result.is_err());
    assert!(result.unwrap_err().message.contains("unknown type"));
}

#[test]
fn trait_method_unknown_return_type_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = make_trait_def(
        "Bad",
        vec![make_trait_method(
            "bad_method",
            vec![("self", None)],
            Some(TypeAnnotation::Named("Nonexistent".into())),
        )],
    );
    let result = traits.register_trait(&def, &records);
    assert!(result.is_err());
    assert!(result.unwrap_err().message.contains("unknown return type"));
}

#[test]
fn trait_self_return_type_resolves() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = make_trait_def(
        "Cloneable",
        vec![make_trait_method(
            "clone",
            vec![("self", None)],
            Some(TypeAnnotation::Named("Self".into())),
        )],
    );
    let result = traits.register_trait(&def, &records);
    assert!(result.is_ok(), "Self should resolve in trait return type");
    let info = traits.lookup_trait("Cloneable").unwrap();
    // Self maps to the same placeholder as `self` param (TypeVarId(u32::MAX))
    assert_eq!(info.methods[0].return_type, Type::Var(TypeVarId(u32::MAX)));
}

#[test]
fn trait_self_param_type_resolves() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = make_trait_def(
        "Addable",
        vec![make_trait_method(
            "add",
            vec![
                ("self", None),
                ("other", Some(TypeAnnotation::Named("Self".into()))),
            ],
            Some(TypeAnnotation::Named("Self".into())),
        )],
    );
    let result = traits.register_trait(&def, &records);
    assert!(result.is_ok(), "Self should resolve in trait param type");
    let info = traits.lookup_trait("Addable").unwrap();
    // `self` and `other: Self` and return type all map to same placeholder
    let self_ty = Type::Var(TypeVarId(u32::MAX));
    assert_eq!(info.methods[0].param_types[0], self_ty);
    assert_eq!(info.methods[0].param_types[1], self_ty);
    assert_eq!(info.methods[0].return_type, self_ty);
}

#[test]
fn trait_impl_missing_method_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(
            &make_trait_def(
                "Show",
                vec![make_trait_method(
                    "show",
                    vec![("self", None)],
                    Some(TypeAnnotation::Named("String".into())),
                )],
            ),
            &records,
        )
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block("Show", "Int", vec![]))
        .unwrap();

    // Provide no methods — should error about missing `show`
    let methods = BTreeMap::new();
    let result = traits.add_impl_methods(methods);
    assert!(result.is_err());
    let msg = result.unwrap_err().message;
    assert!(msg.contains("missing"), "got: {msg}");
    assert!(msg.contains("`show`"), "got: {msg}");
}

#[test]
fn trait_impl_missing_method_with_default_is_allowed() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(
            &make_trait_def(
                "Show",
                vec![make_trait_method_with_default(
                    "show",
                    vec![("self", None)],
                    Some(TypeAnnotation::Named("String".into())),
                    lit_str("default"),
                )],
            ),
            &records,
        )
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block("Show", "Int", vec![]))
        .unwrap();

    // No explicit methods is OK because `show` has a default body.
    assert!(traits.add_impl_methods(BTreeMap::new()).is_ok());
}

#[test]
fn trait_impl_extra_method_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Empty", vec![]), &records)
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block("Empty", "Int", vec![]))
        .unwrap();

    // Provide a method that doesn't exist in the trait
    let mut methods = BTreeMap::new();
    methods.insert("bogus".to_string(), Type::Int);
    let result = traits.add_impl_methods(methods);
    assert!(result.is_err());
    let msg = result.unwrap_err().message;
    assert!(msg.contains("extra"), "got: {msg}");
    assert!(msg.contains("`bogus`"), "got: {msg}");
}

// Step 6: Row polymorphism error message categories
// ===========================================================================

/// Helper: unify two closed rows with a given Reason and return the errors.
fn row_errors_with_reason(
    expected_fields: Vec<(&str, Type)>,
    actual_fields: Vec<(&str, Type)>,
    reason: Reason,
) -> Vec<kea_diag::Diagnostic> {
    let mut u = Unifier::new();
    let expected = RowType::closed(
        expected_fields
            .into_iter()
            .map(|(l, t)| (Label::new(l), t))
            .collect(),
    );
    let actual = RowType::closed(
        actual_fields
            .into_iter()
            .map(|(l, t)| (Label::new(l), t))
            .collect(),
    );
    let prov = Provenance { span: s(), reason };
    u.unify_rows(&expected, &actual, &prov);
    u.errors().to_vec()
}

#[test]
fn error_msg_missing_field_in_record() {
    let errors = row_errors_with_reason(
        vec![("name", Type::String), ("age", Type::Int)],
        vec![("name", Type::String)],
        Reason::LetAnnotation,
    );
    assert_eq!(errors.len(), 1);
    assert!(
        errors[0].message.contains("missing field `age`"),
        "got: {}",
        errors[0].message
    );
    assert_eq!(errors[0].category, kea_diag::Category::MissingField);
    // Help should list expected fields
    assert!(
        errors[0]
            .help
            .as_ref()
            .is_some_and(|h| h.contains("`name`")),
        "help should list expected fields"
    );
}

#[test]
fn error_msg_extra_field_in_record() {
    let errors = row_errors_with_reason(
        vec![("name", Type::String)],
        vec![("name", Type::String), ("temp", Type::Int)],
        Reason::LetAnnotation,
    );
    assert_eq!(errors.len(), 1);
    assert!(
        errors[0].message.contains("unexpected field `temp`"),
        "got: {}",
        errors[0].message
    );
    assert_eq!(errors[0].category, kea_diag::Category::ExtraField);
}

#[test]
fn error_msg_field_type_mismatch() {
    // Field type mismatches go through the type_mismatch_message path, not row errors.
    // They use Reason::RecordField and produce Category::TypeMismatch.
    let errors = row_errors_with_reason(
        vec![("price", Type::Float)],
        vec![("price", Type::String)],
        Reason::LetAnnotation,
    );
    assert_eq!(errors.len(), 1);
    // Field mismatch uses RecordField reason internally
    assert!(
        errors[0].message.contains("price"),
        "got: {}",
        errors[0].message
    );
    assert_eq!(errors[0].category, kea_diag::Category::TypeMismatch);
}

#[test]
fn error_msg_lacks_violation_record_context() {
    // Lacks violation in record context says "field", not "column"
    let r = RowVarId(0);
    let mut u = Unifier::new();
    u.lacks.add(r, Label::new("x"));
    let open = RowType::empty_open(r);
    let closed = RowType::closed(vec![(Label::new("x"), Type::Int)]);
    let prov = Provenance {
        span: s(),
        reason: Reason::LetAnnotation,
    };
    u.unify_rows(&open, &closed, &prov);
    assert!(u.has_errors());
    let msg = &u.errors()[0].message;
    assert!(msg.contains("cannot add field `x`"), "got: {msg}");
    assert!(msg.contains("the record already has a field"), "got: {msg}");
}

#[test]
fn error_msg_function_context_uses_field() {
    // Missing field in function arg context should mention "the function"
    let errors = row_errors_with_reason(
        vec![("x", Type::Int), ("y", Type::Float)],
        vec![("x", Type::Int)],
        Reason::FunctionArg { param_index: 0 },
    );
    assert_eq!(errors.len(), 1);
    assert!(
        errors[0].message.contains("the function"),
        "got: {}",
        errors[0].message
    );
    assert!(
        errors[0].message.contains("missing field `y`"),
        "got: {}",
        errors[0].message
    );
}

#[test]
fn error_msg_function_arg_missing_required_field() {
    // When the function requires a field the argument doesn't provide,
    // the message should say "missing field" not "unexpected field".
    let errors = row_errors_with_reason(
        vec![("x", Type::Int)],
        vec![("x", Type::Int), ("y", Type::Float)],
        Reason::FunctionArg { param_index: 0 },
    );
    assert_eq!(errors.len(), 1);
    assert!(
        errors[0].message.contains("missing field `y`"),
        "got: {}",
        errors[0].message
    );
    assert!(
        errors[0].message.contains("required by"),
        "got: {}",
        errors[0].message
    );
    assert_eq!(errors[0].category, kea_diag::Category::MissingField);
}

#[test]
fn call_missing_field_emits_single_diagnostic() {
    let expr = call(
        lambda(&["r"], field_access(var("r"), "age")),
        vec![anon_record(vec![("name", lit_str("x"))])],
    );
    let (_ty, u) = infer(&expr);

    let missing_age_count = u
        .errors()
        .iter()
        .filter(|d| {
            d.category == kea_diag::Category::MissingField && d.message.contains("field `age`")
        })
        .count();
    assert_eq!(
        missing_age_count,
        1,
        "expected one missing-field diagnostic for `age`, got {:?}",
        u.errors()
    );
}

#[test]
fn error_msg_no_internal_variables_leak() {
    // After unification error, error messages must not contain internal var names
    // like t0, t1, r0, r1.
    let errors = row_errors_with_reason(
        vec![("a", Type::Int)],
        vec![("a", Type::String), ("b", Type::Bool)],
        Reason::LetAnnotation,
    );
    for err in &errors {
        let msg = &err.message;
        // Should not contain raw type variable identifiers
        assert!(!msg.contains("t0"), "message leaks internal var: {msg}");
        assert!(!msg.contains("t1"), "message leaks internal var: {msg}");
        assert!(!msg.contains("r0"), "message leaks internal var: {msg}");
        assert!(!msg.contains("r1"), "message leaks internal var: {msg}");
        assert!(
            !msg.contains("TypeVar"),
            "message leaks internal type: {msg}"
        );
        assert!(
            !msg.contains("RowVar"),
            "message leaks internal type: {msg}"
        );
        if let Some(help) = &err.help {
            assert!(!help.contains("t0"), "help leaks internal var: {help}");
            assert!(!help.contains("r0"), "help leaks internal var: {help}");
        }
    }
}

// ---------------------------------------------------------------------------
// Trait bound enforcement
// ---------------------------------------------------------------------------

#[test]
fn trait_bounds_stored_in_scheme() {
    // Build a TypeScheme with a trait bound: `forall t0. t0 -> t0` where t0: Additive.
    let tv = TypeVarId(0);
    let mut bounds = BTreeMap::new();
    bounds.insert(
        tv,
        std::collections::BTreeSet::from(["Additive".to_string()]),
    );
    let scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds,
        kinds: Default::default(),
        ty: Type::Function(FunctionType {
            params: vec![Type::Var(tv)],
            ret: Box::new(Type::Var(tv)),
            effects: EffectRow::pure(),
        }),
    };
    assert!(!scheme.bounds.is_empty());
    assert!(scheme.bounds[&tv].contains("Additive"));
}

#[test]
fn trait_bounds_survive_instantiation() {
    // Create a scheme with bounds, instantiate it, check bounds transferred.
    let tv = TypeVarId(100);
    let mut bounds = BTreeMap::new();
    bounds.insert(tv, std::collections::BTreeSet::from(["Show".to_string()]));
    let scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds,
        kinds: Default::default(),
        ty: Type::Function(FunctionType {
            params: vec![Type::Var(tv)],
            ret: Box::new(Type::String),
            effects: EffectRow::pure(),
        }),
    };

    let mut unifier = Unifier::new();
    let instantiated = instantiate(&scheme, &mut unifier);

    // The instantiated type should be a function with a fresh type var.
    if let Type::Function(ft) = &instantiated {
        if let Type::Var(fresh_tv) = &ft.params[0] {
            // The fresh type var should have the "Show" bound.
            assert!(
                unifier.trait_bounds.contains_key(fresh_tv),
                "fresh var should have trait bounds"
            );
            assert!(
                unifier.trait_bounds[fresh_tv].contains("Show"),
                "fresh var should have Show bound"
            );
        } else {
            panic!("expected type var, got {:?}", ft.params[0]);
        }
    } else {
        panic!("expected function type, got {:?}", instantiated);
    }
}

#[test]
fn instantiate_dim_quantifier_consumes_fresh_dim_var() {
    let scheme = TypeScheme {
        type_vars: vec![],
        row_vars: vec![],
        dim_vars: vec![DimVarId(99)],
        lacks: BTreeMap::new(),
        bounds: BTreeMap::new(),
        kinds: Default::default(),
        ty: Type::Int,
    };
    // Use deterministic offsets so dim var IDs are predictable.
    let mut unifier = Unifier::with_var_offsets(0, 0, 0);

    let instantiated = instantiate(&scheme, &mut unifier);
    assert_eq!(instantiated, Type::Int);

    // Instantiation consumed one dim var (DimVarId(0)), so next should be 1.
    let next = unifier.fresh_dim_var();
    assert_eq!(next, DimVarId(1));
}

#[test]
fn trait_bounds_checked_against_registry() {
    // Set up a trait registry with `Additive` implemented for List.
    let mut trait_registry = TraitRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: true,
        name: sp("Additive".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![kea_ast::TraitMethod {
            name: sp("sum".to_string()),
            params: vec![],
            return_annotation: None,
            effect_annotation: None,
            where_clause: vec![],
            default_body: None,
            doc: None,
            span: s(),
        }],
    };
    let record_registry = RecordRegistry::new();
    trait_registry
        .register_trait(&trait_def, &record_registry)
        .unwrap();

    // Register impl Additive for List.
    let impl_block = kea_ast::ImplBlock {
        trait_name: sp("Additive".to_string()),
        type_name: sp("List".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    trait_registry.register_trait_impl(&impl_block).unwrap();
    // Add dummy methods to satisfy the impl.
    trait_registry
        .add_impl_methods(BTreeMap::from([("sum".to_string(), Type::Int)]))
        .unwrap();

    // Create a scheme with `t0: Additive`, instantiate it, then unify t0 with List(Int).
    let tv = TypeVarId(100);
    let mut bounds = BTreeMap::new();
    bounds.insert(
        tv,
        std::collections::BTreeSet::from(["Additive".to_string()]),
    );
    let scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds,
        kinds: Default::default(),
        ty: Type::Var(tv),
    };

    let mut unifier = Unifier::new();
    let ty = instantiate(&scheme, &mut unifier);

    // Unify with List(Int) — satisfies the bound.
    let prov = crate::Provenance {
        span: s(),
        reason: crate::Reason::LetAnnotation,
    };
    unifier.unify(&ty, &Type::List(Box::new(Type::Int)), &prov);
    assert!(!unifier.has_errors());

    // Check bounds — should succeed.
    unifier.check_trait_bounds(&trait_registry);
    assert!(!unifier.has_errors(), "List should satisfy Additive");
}

#[test]
fn trait_bounds_violation_produces_error() {
    // Set up a trait registry with `Additive` but NO impl for Int.
    let mut trait_registry = TraitRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: true,
        name: sp("Additive".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    let record_registry = RecordRegistry::new();
    trait_registry
        .register_trait(&trait_def, &record_registry)
        .unwrap();

    // Create a scheme with `t0: Additive`, instantiate, unify with Int.
    let tv = TypeVarId(100);
    let mut bounds = BTreeMap::new();
    bounds.insert(
        tv,
        std::collections::BTreeSet::from(["Additive".to_string()]),
    );
    let scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds,
        kinds: Default::default(),
        ty: Type::Var(tv),
    };

    let mut unifier = Unifier::new();
    let ty = instantiate(&scheme, &mut unifier);

    // Unify with Int — no impl exists.
    let prov = crate::Provenance {
        span: s(),
        reason: crate::Reason::LetAnnotation,
    };
    unifier.unify(&ty, &Type::Int, &prov);
    assert!(!unifier.has_errors());

    // Check bounds — should fail.
    unifier.check_trait_bounds(&trait_registry);
    assert!(unifier.has_errors(), "Int should NOT satisfy Additive");
    let msg = &unifier.errors()[0].message;
    assert!(msg.contains("Int"), "error should mention the type: {msg}");
    assert!(
        msg.contains("Additive"),
        "error should mention the trait: {msg}"
    );
}

#[test]
fn ambiguous_trait_bound_reports_error_and_skips_evidence_sites() {
    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();

    let from_trait = kea_ast::TraitDef {
        public: true,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&from_trait, &records).unwrap();

    for source in ["String", "Float"] {
        let imp = kea_ast::ImplBlock {
            trait_name: sp("From".to_string()),
            type_name: sp("Int".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![kea_ast::WhereItem::TypeAssignment {
                name: sp("Source".to_string()),
                ty: sp(TypeAnnotation::Named(source.to_string())),
            }],
        };
        traits.register_trait_impl(&imp).unwrap();
    }

    let tv = TypeVarId(7500);
    let scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds: BTreeMap::from([(tv, std::collections::BTreeSet::from(["From".to_string()]))]),
        kinds: Default::default(),
        ty: Type::Function(FunctionType {
            params: vec![Type::Var(tv)],
            ret: Box::new(Type::String),
            effects: EffectRow::pure(),
        }),
    };
    env.bind("show".to_string(), scheme);

    let expr = call(var("show"), vec![lit_int(42)]);
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sum_types);
    assert_eq!(ty, Type::String);
    assert!(!unifier.has_errors());

    unifier.check_trait_bounds(&traits);
    assert!(unifier.has_errors());
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message == "ambiguous impl resolution for trait `From` on type `Int`"),
        "expected ambiguity error, got {:?}",
        unifier
            .errors()
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );

    let annotations = unifier.take_type_annotations();
    assert!(
        !annotations.evidence_sites.contains_key(&expr.span),
        "ambiguous trait bound should not emit runtime evidence sites"
    );
}

#[test]
fn existential_param_check_reports_ambiguous_trait_impl() {
    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();

    let from_trait = kea_ast::TraitDef {
        public: true,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&from_trait, &records).unwrap();

    for source in ["String", "Float"] {
        let imp = kea_ast::ImplBlock {
            trait_name: sp("From".to_string()),
            type_name: sp("Int".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![kea_ast::WhereItem::TypeAssignment {
                name: sp("Source".to_string()),
                ty: sp(TypeAnnotation::Named(source.to_string())),
            }],
        };
        traits.register_trait_impl(&imp).unwrap();
    }

    env.bind(
        "accept".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Existential {
                bounds: vec!["From".to_string()],
                associated_types: BTreeMap::new(),
            }],
            ret: Box::new(Type::Unit),
            effects: EffectRow::pure(),
        })),
    );

    let expr = call(var("accept"), vec![lit_int(42)]);
    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sum_types);
    unifier.check_trait_bounds(&traits);

    assert!(unifier.has_errors());
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message == "ambiguous impl resolution for trait `From` on type `Int`"),
        "expected ambiguity diagnostic, got {:?}",
        unifier
            .errors()
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );
}

#[test]
fn call_site_evidence_annotations_emitted_after_trait_check() {
    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();

    let display_trait = kea_ast::TraitDef {
        public: true,
        name: sp("Display".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&display_trait, &records).unwrap();
    let display_int_impl = kea_ast::ImplBlock {
        trait_name: sp("Display".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    traits.register_trait_impl(&display_int_impl).unwrap();
    traits.add_impl_methods(BTreeMap::new()).unwrap();

    let tv = TypeVarId(7000);
    let show_scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds: BTreeMap::from([(
            tv,
            std::collections::BTreeSet::from(["Display".to_string()]),
        )]),
        kinds: Default::default(),
        ty: Type::Function(FunctionType {
            params: vec![Type::Var(tv)],
            ret: Box::new(Type::String),
            effects: EffectRow::pure(),
        }),
    };
    env.bind("show".to_string(), show_scheme);

    let expr = call(var("show"), vec![lit_int(42)]);
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sum_types);
    assert_eq!(ty, Type::String);
    assert!(!unifier.has_errors());

    // Evidence is resolved after final substitution in trait-bound checking.
    unifier.check_trait_bounds(&traits);
    assert!(!unifier.has_errors());
    let annotations = unifier.take_type_annotations();
    let sites = annotations
        .evidence_sites
        .get(&expr.span)
        .expect("expected evidence site for call");
    assert!(
        sites
            .iter()
            .any(|site| site.trait_name == "Display" && site.type_name == "Int"),
        "expected Display evidence for Int at call site, got {sites:?}"
    );
}

#[test]
fn supertrait_bound_requires_supertrait_impl() {
    let mut traits = TraitRegistry::new();
    let records = RecordRegistry::new();

    let eq_trait = kea_ast::TraitDef {
        public: true,
        name: sp("Eq".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&eq_trait, &records).unwrap();

    let orderable_trait = kea_ast::TraitDef {
        public: true,
        name: sp("Orderable".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![sp("Eq".to_string())],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&orderable_trait, &records).unwrap();

    // Only Orderable for Int, no Eq for Int.
    let orderable_int_impl = kea_ast::ImplBlock {
        trait_name: sp("Orderable".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    traits.register_trait_impl(&orderable_int_impl).unwrap();
    traits.add_impl_methods(BTreeMap::new()).unwrap();

    let tv = TypeVarId(7100);
    let scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds: BTreeMap::from([(
            tv,
            std::collections::BTreeSet::from(["Orderable".to_string()]),
        )]),
        kinds: Default::default(),
        ty: Type::Var(tv),
    };
    let mut unifier = Unifier::new();
    let ty = instantiate(&scheme, &mut unifier);
    let prov = crate::Provenance {
        span: s(),
        reason: crate::Reason::LetAnnotation,
    };
    unifier.unify(&ty, &Type::Int, &prov);
    unifier.check_trait_bounds(&traits);
    assert!(
        unifier.has_errors(),
        "Orderable should not be satisfied when Eq supertrait impl is missing"
    );
}

#[test]
fn call_site_evidence_annotations_include_supertraits() {
    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();

    let eq_trait = kea_ast::TraitDef {
        public: true,
        name: sp("Eq".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&eq_trait, &records).unwrap();

    let orderable_trait = kea_ast::TraitDef {
        public: true,
        name: sp("Orderable".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![sp("Eq".to_string())],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&orderable_trait, &records).unwrap();

    let eq_int_impl = kea_ast::ImplBlock {
        trait_name: sp("Eq".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    traits.register_trait_impl(&eq_int_impl).unwrap();
    traits.add_impl_methods(BTreeMap::new()).unwrap();

    let orderable_int_impl = kea_ast::ImplBlock {
        trait_name: sp("Orderable".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    traits.register_trait_impl(&orderable_int_impl).unwrap();
    traits.add_impl_methods(BTreeMap::new()).unwrap();

    let tv = TypeVarId(7200);
    let scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds: BTreeMap::from([(
            tv,
            std::collections::BTreeSet::from(["Orderable".to_string()]),
        )]),
        kinds: Default::default(),
        ty: Type::Function(FunctionType {
            params: vec![Type::Var(tv)],
            ret: Box::new(Type::String),
            effects: EffectRow::pure(),
        }),
    };
    env.bind("show".to_string(), scheme);

    let expr = call(var("show"), vec![lit_int(42)]);
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sum_types);
    assert_eq!(ty, Type::String);
    assert!(!unifier.has_errors());

    unifier.check_trait_bounds(&traits);
    assert!(!unifier.has_errors());
    let annotations = unifier.take_type_annotations();
    let sites = annotations
        .evidence_sites
        .get(&expr.span)
        .expect("expected evidence site for call");
    assert!(
        sites
            .iter()
            .any(|site| site.trait_name == "Orderable" && site.type_name == "Int"),
        "expected Orderable evidence for Int at call site, got {sites:?}"
    );
    assert!(
        sites
            .iter()
            .any(|site| site.trait_name == "Eq" && site.type_name == "Int"),
        "expected Eq supertrait evidence for Int at call site, got {sites:?}"
    );
}

#[test]
fn call_site_evidence_annotations_expand_parametric_impl_bounds() {
    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();

    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block("Show", "Int", vec![]))
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block_with_params(
            "Show",
            "List",
            vec!["t"],
            vec![kea_ast::WhereItem::TraitBound(kea_ast::TraitBound {
                type_var: sp("t".to_string()),
                trait_name: sp("Show".to_string()),
            })],
            vec![],
        ))
        .unwrap();
    traits.add_impl_methods(BTreeMap::new()).unwrap();

    let tv = TypeVarId(7300);
    let show_scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds: BTreeMap::from([(tv, std::collections::BTreeSet::from(["Show".to_string()]))]),
        kinds: Default::default(),
        ty: Type::Function(FunctionType {
            params: vec![Type::Var(tv)],
            ret: Box::new(Type::String),
            effects: EffectRow::pure(),
        }),
    };
    env.bind("show".to_string(), show_scheme);

    let expr = call(var("show"), vec![list(vec![lit_int(1), lit_int(2)])]);
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sum_types);
    assert_eq!(ty, Type::String);
    assert!(!unifier.has_errors());

    unifier.check_trait_bounds(&traits);
    assert!(!unifier.has_errors());
    let annotations = unifier.take_type_annotations();
    let sites = annotations
        .evidence_sites
        .get(&expr.span)
        .expect("expected evidence site for call");

    assert!(
        sites
            .iter()
            .any(|site| site.trait_name == "Show" && site.type_name == "List"),
        "expected Show evidence for List at call site, got {sites:?}"
    );
    assert!(
        sites
            .iter()
            .any(|site| site.trait_name == "Show" && site.type_name == "Int"),
        "expected transitive Show evidence for Int at call site, got {sites:?}"
    );
}

#[test]
fn call_site_evidence_annotations_expand_nested_parametric_bounds() {
    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();

    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block("Show", "Int", vec![]))
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block_with_params(
            "Show",
            "List",
            vec!["t"],
            vec![kea_ast::WhereItem::TraitBound(kea_ast::TraitBound {
                type_var: sp("t".to_string()),
                trait_name: sp("Show".to_string()),
            })],
            vec![],
        ))
        .unwrap();
    traits.add_impl_methods(BTreeMap::new()).unwrap();

    let tv = TypeVarId(7400);
    let show_scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds: BTreeMap::from([(tv, std::collections::BTreeSet::from(["Show".to_string()]))]),
        kinds: Default::default(),
        ty: Type::Function(FunctionType {
            params: vec![Type::Var(tv)],
            ret: Box::new(Type::String),
            effects: EffectRow::pure(),
        }),
    };
    env.bind("show".to_string(), show_scheme);

    let expr = call(
        var("show"),
        vec![list(vec![list(vec![lit_int(1), lit_int(2)])])],
    );
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sum_types);
    assert_eq!(ty, Type::String);
    assert!(!unifier.has_errors());

    unifier.check_trait_bounds(&traits);
    assert!(!unifier.has_errors());
    let annotations = unifier.take_type_annotations();
    let sites = annotations
        .evidence_sites
        .get(&expr.span)
        .expect("expected evidence site for call");

    let show_list_count = sites
        .iter()
        .filter(|site| site.trait_name == "Show" && site.type_name == "List")
        .count();
    assert_eq!(
        show_list_count, 1,
        "evidence should dedupe repeated Show/List requirements: {sites:?}"
    );
    assert!(
        sites
            .iter()
            .any(|site| site.trait_name == "Show" && site.type_name == "Int"),
        "expected nested transitive Show evidence for Int, got {sites:?}"
    );
}

#[test]
fn trait_qualified_call_uses_trait_method_signature_and_evidence() {
    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();

    traits
        .register_trait(
            &make_trait_def(
                "Show",
                vec![make_trait_method(
                    "show",
                    vec![("self", None)],
                    Some(TypeAnnotation::Named("String".into())),
                )],
            ),
            &records,
        )
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block("Show", "Int", vec![]))
        .unwrap();

    let expr = call(field_access(var("Show"), "show"), vec![lit_int(42)]);
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sum_types);
    assert_eq!(ty, Type::String);
    assert!(!unifier.has_errors());

    unifier.check_trait_bounds(&traits);
    assert!(!unifier.has_errors());
    let annotations = unifier.take_type_annotations();
    let sites = annotations
        .evidence_sites
        .get(&expr.span)
        .expect("expected evidence site for trait-qualified call");
    assert!(
        sites
            .iter()
            .any(|site| site.trait_name == "Show" && site.type_name == "Int"),
        "expected Show evidence for Int at call site, got {sites:?}"
    );
}

#[test]
fn trait_qualified_lookup_reports_missing_trait_method() {
    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();
    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();

    let expr = field_access(var("Show"), "show");
    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sum_types);
    assert!(unifier.has_errors());
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("trait `Show` has no method `show`")),
        "expected missing trait method diagnostic, got {:?}",
        unifier
            .errors()
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );
}

#[test]
fn module_name_collision_wins_over_trait_qualified_lookup() {
    let mut env = TypeEnv::new();
    let mut traits = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();

    env.register_module_alias("Show", "Kea.Show");
    env.register_module_function("Kea.Show", "show");
    env.register_module_type_scheme(
        "Kea.Show",
        "show",
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })),
        Effects::pure_deterministic(),
    );

    traits
        .register_trait(
            &make_trait_def(
                "Show",
                vec![make_trait_method(
                    "show",
                    vec![("self", None)],
                    Some(TypeAnnotation::Named("String".into())),
                )],
            ),
            &records,
        )
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block("Show", "Int", vec![]))
        .unwrap();

    let expr = call(field_access(var("Show"), "show"), vec![lit_int(42)]);
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sum_types);
    assert_eq!(ty, Type::Int, "module member should win over trait lookup");
    assert!(!unifier.has_errors());
}

#[test]
fn apply_where_clause_attaches_bounds() {
    // Simulate what happens when processing `fn total(x) where x: Additive { x }`.
    // After desugaring + inference, we get a scheme: forall t0. (t0) -> t0.
    // apply_where_clause should attach {t0: Additive}.
    let tv = TypeVarId(0);
    let mut scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds: BTreeMap::new(),
        kinds: Default::default(),
        ty: Type::Function(FunctionType {
            params: vec![Type::Var(tv)],
            ret: Box::new(Type::Var(tv)),
            effects: EffectRow::pure(),
        }),
    };

    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("total".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("x".to_string())),
            annotation: None,
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: var("x"),
        span: s(),
        where_clause: vec![TraitBound {
            type_var: sp("x".to_string()),
            trait_name: sp("Additive".to_string()),
        }],
        testing: None,
        testing_tags: Vec::new(),
    };

    let subst = kea_types::Substitution::new();
    apply_where_clause(&mut scheme, &fn_decl, &subst);

    assert!(
        scheme.bounds.contains_key(&tv),
        "scheme should have bounds on t0"
    );
    assert!(
        scheme.bounds[&tv].contains("Additive"),
        "t0 should have Additive bound"
    );
}

#[test]
fn validate_where_clause_traits_reports_unknown_trait() {
    let traits = TraitRegistry::new();
    let where_clause = vec![TraitBound {
        type_var: sp("x".to_string()),
        trait_name: sp("UnknownTrait".to_string()),
    }];
    let diags = validate_where_clause_traits(&where_clause, &traits);
    assert_eq!(diags.len(), 1);
    assert!(
        diags[0]
            .message
            .contains("trait `UnknownTrait` is not defined")
    );
}

#[test]
fn validate_where_clause_traits_reports_ambiguous_multi_param_bound() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let trait_def = TraitDef {
        public: false,
        name: sp("BiLike".to_string()),
        doc: None,
        type_params: vec![
            TraitTypeParam {
                name: sp("F".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
            TraitTypeParam {
                name: sp("G".to_string()),
                kind: kind_star(),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&trait_def, &records).unwrap();

    let where_clause = vec![TraitBound {
        type_var: sp("T".to_string()),
        trait_name: sp("BiLike".to_string()),
    }];
    let diags = validate_where_clause_traits(&where_clause, &traits);
    assert_eq!(diags.len(), 1);
    assert!(
        diags[0]
            .message
            .contains("ambiguous bound `T`: trait `BiLike` has multiple type parameters")
    );
}

#[test]
fn validate_where_clause_traits_allows_matching_multi_param_bound_name() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let trait_def = TraitDef {
        public: false,
        name: sp("BiLike".to_string()),
        doc: None,
        type_params: vec![
            TraitTypeParam {
                name: sp("F".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
            TraitTypeParam {
                name: sp("G".to_string()),
                kind: kind_star(),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&trait_def, &records).unwrap();

    let where_clause = vec![TraitBound {
        type_var: sp("G".to_string()),
        trait_name: sp("BiLike".to_string()),
    }];
    let diags = validate_where_clause_traits(&where_clause, &traits);
    assert!(
        diags.is_empty(),
        "expected no diagnostics for matching bound, got: {diags:?}"
    );
}

#[test]
fn seed_fn_where_type_params_reports_unknown_trait() {
    let trait_registry = TraitRegistry::new();
    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("demo".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("x".to_string())),
            annotation: None,
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: var("x"),
        span: s(),
        where_clause: vec![TraitBound {
            type_var: sp("F".to_string()),
            trait_name: sp("UnknownTrait".to_string()),
        }],
        testing: None,
        testing_tags: Vec::new(),
    };

    let mut unifier = Unifier::new();
    seed_fn_where_type_params(&fn_decl, &trait_registry, &mut unifier);
    assert!(unifier.has_errors());
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("trait `UnknownTrait` is not defined"))
    );
}

#[test]
fn seed_fn_where_type_params_registers_kinded_constructor_var() {
    let mut trait_registry = TraitRegistry::new();
    let records = RecordRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: true,
        name: sp("Applicative".to_string()),
        doc: None,
        type_params: vec![kea_ast::TraitTypeParam {
            name: sp("F".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    trait_registry.register_trait(&trait_def, &records).unwrap();

    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("demo".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("xs".to_string())),
            annotation: None,
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: var("xs"),
        span: s(),
        where_clause: vec![TraitBound {
            type_var: sp("F".to_string()),
            trait_name: sp("Applicative".to_string()),
        }],
        testing: None,
        testing_tags: Vec::new(),
    };

    let mut unifier = Unifier::new();
    seed_fn_where_type_params(&fn_decl, &trait_registry, &mut unifier);

    let Some(Type::Var(f_tv)) = unifier.annotation_type_param("F").cloned() else {
        panic!("F should be seeded as a type variable");
    };
    assert_eq!(unifier.type_var_kinds.get(&f_tv), Some(&Kind::Star));
    assert!(
        unifier
            .trait_bounds
            .get(&f_tv)
            .is_some_and(|bounds| bounds.contains("Applicative"))
    );
}

#[test]
fn seed_fn_where_type_params_uses_matching_kind_for_multi_param_trait() {
    let mut trait_registry = TraitRegistry::new();
    let records = RecordRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: true,
        name: sp("BiLike".to_string()),
        doc: None,
        type_params: vec![
            kea_ast::TraitTypeParam {
                name: sp("F".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
            kea_ast::TraitTypeParam {
                name: sp("G".to_string()),
                kind: kind_star(),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    trait_registry.register_trait(&trait_def, &records).unwrap();

    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("demo".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("xs".to_string())),
            annotation: None,
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: var("xs"),
        span: s(),
        where_clause: vec![TraitBound {
            type_var: sp("F".to_string()),
            trait_name: sp("BiLike".to_string()),
        }],
        testing: None,
        testing_tags: Vec::new(),
    };

    let mut unifier = Unifier::new();
    seed_fn_where_type_params(&fn_decl, &trait_registry, &mut unifier);
    assert!(
        !unifier.has_errors(),
        "unexpected errors: {:?}",
        unifier.errors()
    );

    let Some(Type::Var(f_tv)) = unifier.annotation_type_param("F").cloned() else {
        panic!("F should be seeded as a type variable");
    };
    assert_eq!(unifier.type_var_kinds.get(&f_tv), Some(&Kind::Star));
}

#[test]
fn seed_fn_where_type_params_uses_second_kind_when_bound_name_matches() {
    let mut trait_registry = TraitRegistry::new();
    let records = RecordRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: true,
        name: sp("BiLike".to_string()),
        doc: None,
        type_params: vec![
            kea_ast::TraitTypeParam {
                name: sp("F".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
            kea_ast::TraitTypeParam {
                name: sp("G".to_string()),
                kind: kind_star(),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    trait_registry.register_trait(&trait_def, &records).unwrap();

    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("demo".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("xs".to_string())),
            annotation: None,
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: var("xs"),
        span: s(),
        where_clause: vec![TraitBound {
            type_var: sp("G".to_string()),
            trait_name: sp("BiLike".to_string()),
        }],
        testing: None,
        testing_tags: Vec::new(),
    };

    let mut unifier = Unifier::new();
    seed_fn_where_type_params(&fn_decl, &trait_registry, &mut unifier);
    assert!(
        !unifier.has_errors(),
        "unexpected errors: {:?}",
        unifier.errors()
    );

    let Some(Type::Var(g_tv)) = unifier.annotation_type_param("G").cloned() else {
        panic!("G should be seeded as a type variable");
    };
    assert_eq!(unifier.type_var_kinds.get(&g_tv), Some(&Kind::Star));
}

#[test]
fn seed_fn_where_type_params_errors_for_ambiguous_multi_param_trait_bound() {
    let mut trait_registry = TraitRegistry::new();
    let records = RecordRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: true,
        name: sp("BiLike".to_string()),
        doc: None,
        type_params: vec![
            kea_ast::TraitTypeParam {
                name: sp("F".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
            kea_ast::TraitTypeParam {
                name: sp("G".to_string()),
                kind: kind_star(),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    trait_registry.register_trait(&trait_def, &records).unwrap();

    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("demo".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("xs".to_string())),
            annotation: None,
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: var("xs"),
        span: s(),
        where_clause: vec![TraitBound {
            type_var: sp("T".to_string()),
            trait_name: sp("BiLike".to_string()),
        }],
        testing: None,
        testing_tags: Vec::new(),
    };

    let mut unifier = Unifier::new();
    seed_fn_where_type_params(&fn_decl, &trait_registry, &mut unifier);
    assert!(unifier.has_errors(), "expected ambiguous bound error");
    assert!(
        unifier.errors().iter().any(|d| d
            .message
            .contains("ambiguous bound `T`: trait `BiLike` has multiple type parameters")),
        "unexpected diagnostics: {:?}",
        unifier.errors()
    );
}

#[test]
fn fn_decl_annotations_support_constructor_application_type_vars() {
    let mut trait_registry = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: true,
        name: sp("Applicative".to_string()),
        doc: None,
        type_params: vec![kea_ast::TraitTypeParam {
            name: sp("F".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    trait_registry.register_trait(&trait_def, &records).unwrap();

    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("identity_list".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("items".to_string())),
            annotation: Some(sp(TypeAnnotation::Applied(
                "List".to_string(),
                vec![TypeAnnotation::Applied(
                    "F".to_string(),
                    vec![TypeAnnotation::Named("a".to_string())],
                )],
            ))),
            default: None,
        }],
        return_annotation: Some(sp(TypeAnnotation::Applied(
            "List".to_string(),
            vec![TypeAnnotation::Applied(
                "F".to_string(),
                vec![TypeAnnotation::Named("a".to_string())],
            )],
        ))),
        effect_annotation: None,
        body: var("items"),
        span: s(),
        where_clause: vec![TraitBound {
            type_var: sp("F".to_string()),
            trait_name: sp("Applicative".to_string()),
        }],
        testing: None,
        testing_tags: Vec::new(),
    };

    let expr = fn_decl.to_let_expr();
    let mut env = TypeEnv::new();
    let mut unifier = Unifier::new();
    seed_fn_where_type_params(&fn_decl, &trait_registry, &mut unifier);
    let Some(Type::Var(f_tv)) = unifier.annotation_type_param("F").cloned() else {
        panic!("F should be seeded as a type variable");
    };

    let _ = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &trait_registry,
        &sum_types,
    );
    assert!(
        !unifier.has_errors(),
        "unexpected type errors: {:?}",
        unifier.errors()
    );

    let scheme = env
        .lookup("identity_list")
        .expect("function should be bound");
    assert!(
        scheme
            .bounds
            .get(&f_tv)
            .is_some_and(|bounds| bounds.contains("Applicative")),
        "generalized scheme should preserve Applicative bound on F"
    );
    assert_eq!(scheme.kinds.get(&f_tv), Some(&Kind::Star));
}

#[test]
fn trait_method_annotations_support_constructor_type_params() {
    let mut trait_registry = TraitRegistry::new();
    let records = RecordRegistry::new();

    let trait_def = kea_ast::TraitDef {
        public: true,
        name: sp("Applicative".to_string()),
        doc: None,
        type_params: vec![kea_ast::TraitTypeParam {
            name: sp("F".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![kea_ast::TraitMethod {
            name: sp("pure".to_string()),
            params: vec![Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("value".to_string())),
                annotation: Some(sp(TypeAnnotation::Named("a".to_string()))),
                default: None,
            }],
            return_annotation: Some(sp(TypeAnnotation::Applied(
                "F".to_string(),
                vec![TypeAnnotation::Named("a".to_string())],
            ))),
            effect_annotation: None,
            where_clause: vec![],
            default_body: None,
            doc: None,
            span: s(),
        }],
    };

    trait_registry.register_trait(&trait_def, &records).unwrap();
    let applicative = trait_registry
        .lookup_trait("Applicative")
        .expect("Applicative should be registered");
    let pure = applicative
        .methods
        .iter()
        .find(|m| m.name == "pure")
        .expect("pure method");

    let Type::Var(arg_tv) = pure.param_types[0] else {
        panic!("pure arg should be a type var");
    };
    let Type::App(ctor, args) = &pure.return_type else {
        panic!("pure return should be constructor application");
    };
    assert_eq!(**ctor, Type::Var(TypeVarId(u32::MAX)));
    assert_eq!(args.len(), 1);
    assert_eq!(args[0], Type::Var(arg_tv));
}

#[test]
fn trait_method_where_clause_propagates_kind_and_trait_bound() {
    let mut env = TypeEnv::new();
    let mut trait_registry = TraitRegistry::new();
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();

    let applicative = kea_ast::TraitDef {
        public: true,
        name: sp("Applicative".to_string()),
        doc: None,
        type_params: vec![kea_ast::TraitTypeParam {
            name: sp("F".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    trait_registry
        .register_trait(&applicative, &records)
        .unwrap();

    let traversable = kea_ast::TraitDef {
        public: true,
        name: sp("Traversable".to_string()),
        doc: None,
        type_params: vec![kea_ast::TraitTypeParam {
            name: sp("T".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![kea_ast::TraitMethod {
            name: sp("traverse".to_string()),
            params: vec![
                Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("value".to_string())),
                    annotation: Some(sp(TypeAnnotation::Applied(
                        "T".to_string(),
                        vec![TypeAnnotation::Named("a".to_string())],
                    ))),
                    default: None,
                },
                Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("f".to_string())),
                    annotation: Some(sp(TypeAnnotation::Function(
                        vec![TypeAnnotation::Named("a".to_string())],
                        Box::new(TypeAnnotation::Applied(
                            "F".to_string(),
                            vec![TypeAnnotation::Named("b".to_string())],
                        )),
                    ))),
                    default: None,
                },
            ],
            return_annotation: Some(sp(TypeAnnotation::Applied(
                "F".to_string(),
                vec![TypeAnnotation::Applied(
                    "T".to_string(),
                    vec![TypeAnnotation::Named("b".to_string())],
                )],
            ))),
            effect_annotation: None,
            where_clause: vec![TraitBound {
                type_var: sp("F".to_string()),
                trait_name: sp("Applicative".to_string()),
            }],
            default_body: None,
            doc: None,
            span: s(),
        }],
    };
    trait_registry
        .register_trait(&traversable, &records)
        .unwrap();

    let expr = field_access(var("Traversable"), "traverse");
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &trait_registry,
        &sum_types,
    );
    assert!(
        !unifier.has_errors(),
        "unexpected errors: {:?}",
        unifier.errors()
    );

    let applicative_var = unifier
        .trait_bounds
        .iter()
        .find_map(|(tv, bounds)| bounds.contains("Applicative").then_some(*tv))
        .expect("expected method-level Applicative bound");
    let traversable_var = unifier
        .trait_bounds
        .iter()
        .find_map(|(tv, bounds)| bounds.contains("Traversable").then_some(*tv))
        .expect("expected self Traversable bound");

    let expected_hkt_kind = Kind::Star;
    assert_eq!(
        unifier.type_var_kinds.get(&applicative_var),
        Some(&expected_hkt_kind)
    );
    assert_eq!(
        unifier.type_var_kinds.get(&traversable_var),
        Some(&expected_hkt_kind)
    );
}

#[test]
fn trait_method_where_clause_allows_matching_param_on_multi_param_trait() {
    let mut trait_registry = TraitRegistry::new();
    let records = RecordRegistry::new();

    let bi_constraint = kea_ast::TraitDef {
        public: true,
        name: sp("BiConstraint".to_string()),
        doc: None,
        type_params: vec![
            kea_ast::TraitTypeParam {
                name: sp("F".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
            kea_ast::TraitTypeParam {
                name: sp("G".to_string()),
                kind: kind_star(),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    trait_registry
        .register_trait(&bi_constraint, &records)
        .unwrap();

    let uses = kea_ast::TraitDef {
        public: true,
        name: sp("Uses".to_string()),
        doc: None,
        type_params: vec![
            kea_ast::TraitTypeParam {
                name: sp("F".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
            kea_ast::TraitTypeParam {
                name: sp("G".to_string()),
                kind: kind_star(),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![kea_ast::TraitMethod {
            name: sp("keep".to_string()),
            params: vec![Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("value".to_string())),
                annotation: Some(sp(TypeAnnotation::Named("G".to_string()))),
                default: None,
            }],
            return_annotation: Some(sp(TypeAnnotation::Named("G".to_string()))),
            effect_annotation: None,
            where_clause: vec![TraitBound {
                type_var: sp("G".to_string()),
                trait_name: sp("BiConstraint".to_string()),
            }],
            default_body: None,
            doc: None,
            span: s(),
        }],
    };

    trait_registry
        .register_trait(&uses, &records)
        .expect("matching multi-parameter where bound should register");
}

#[test]
fn trait_method_where_clause_errors_for_ambiguous_multi_param_bound() {
    let mut trait_registry = TraitRegistry::new();
    let records = RecordRegistry::new();

    let bi_constraint = kea_ast::TraitDef {
        public: true,
        name: sp("BiConstraint".to_string()),
        doc: None,
        type_params: vec![
            kea_ast::TraitTypeParam {
                name: sp("F".to_string()),
                kind: kind_arrow(kind_star(), kind_star()),
            },
            kea_ast::TraitTypeParam {
                name: sp("G".to_string()),
                kind: kind_star(),
            },
        ],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    trait_registry
        .register_trait(&bi_constraint, &records)
        .unwrap();

    let uses = kea_ast::TraitDef {
        public: true,
        name: sp("Uses".to_string()),
        doc: None,
        type_params: vec![kea_ast::TraitTypeParam {
            name: sp("H".to_string()),
            kind: kind_arrow(kind_star(), kind_star()),
        }],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![kea_ast::TraitMethod {
            name: sp("keep".to_string()),
            params: vec![Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("value".to_string())),
                annotation: Some(sp(TypeAnnotation::Named("H".to_string()))),
                default: None,
            }],
            return_annotation: Some(sp(TypeAnnotation::Named("H".to_string()))),
            effect_annotation: None,
            where_clause: vec![TraitBound {
                type_var: sp("T".to_string()),
                trait_name: sp("BiConstraint".to_string()),
            }],
            default_body: None,
            doc: None,
            span: s(),
        }],
    };

    let err = trait_registry
        .register_trait(&uses, &records)
        .expect_err("ambiguous where bound should fail registration");
    assert!(
        err.message
            .contains("ambiguous bound `T`: trait `BiConstraint` has multiple type parameters")
    );
}

#[test]
fn generalize_preserves_trait_bounds() {
    // Set up: fresh type var t0 with trait bound "Show".
    let mut unifier = Unifier::new();
    let tv = unifier.fresh_type_var();
    unifier.add_trait_bound(tv, "Show".to_string());

    let env = TypeEnv::new();

    // Generalize t0 -> t0.
    let ty = Type::Function(FunctionType {
        params: vec![Type::Var(tv)],
        ret: Box::new(Type::Var(tv)),
        effects: EffectRow::pure(),
    });
    let scheme = generalize(
        &ty,
        &env,
        &unifier.substitution,
        &unifier.lacks,
        &unifier.trait_bounds,
        &unifier.type_var_kinds,
    );

    assert!(scheme.type_vars.contains(&tv));
    assert!(
        scheme.bounds.contains_key(&tv),
        "generalized scheme should preserve trait bounds"
    );
    assert!(scheme.bounds[&tv].contains("Show"), "bound should be Show");
}

#[test]
fn multiple_trait_bounds_enforced() {
    // Two bounds on the same type var: Additive + Show.
    let mut trait_registry = TraitRegistry::new();
    let record_registry = RecordRegistry::new();
    for name in ["Additive", "Show"] {
        let trait_def = kea_ast::TraitDef {
            public: true,
            name: sp(name.to_string()),
            doc: None,
            type_params: vec![],
            supertraits: vec![],
            fundeps: vec![],
            associated_types: vec![],
            methods: vec![],
        };
        trait_registry
            .register_trait(&trait_def, &record_registry)
            .unwrap();
    }

    // Only register impl Additive for Int, NOT Show for Int.
    let impl_block = kea_ast::ImplBlock {
        trait_name: sp("Additive".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    trait_registry.register_trait_impl(&impl_block).unwrap();
    trait_registry.add_impl_methods(BTreeMap::new()).unwrap();

    let tv = TypeVarId(100);
    let mut bounds = BTreeMap::new();
    bounds.insert(
        tv,
        std::collections::BTreeSet::from(["Additive".to_string(), "Show".to_string()]),
    );
    let scheme = TypeScheme {
        type_vars: vec![tv],
        row_vars: vec![],
        dim_vars: vec![],
        lacks: BTreeMap::new(),
        bounds,
        kinds: Default::default(),
        ty: Type::Var(tv),
    };

    let mut unifier = Unifier::new();
    let ty = instantiate(&scheme, &mut unifier);
    let prov = crate::Provenance {
        span: s(),
        reason: crate::Reason::LetAnnotation,
    };
    unifier.unify(&ty, &Type::Int, &prov);

    // Check: Additive should pass, Show should fail.
    unifier.check_trait_bounds(&trait_registry);
    assert!(unifier.has_errors());
    assert_eq!(unifier.errors().len(), 1, "only Show should fail");
    assert!(unifier.errors()[0].message.contains("Show"));
}

/// Full integration test: build Let(Lambda) → infer → apply_where_clause → instantiate → check.
/// This mimics the exact MCP server flow without depending on kea-syntax.
#[test]
fn trait_bound_enforcement_end_to_end() {
    // 1. Set up trait registry with Additive implemented for Int only.
    let mut trait_registry = TraitRegistry::new();
    let record_registry = RecordRegistry::new();
    let trait_def = kea_ast::TraitDef {
        public: true,
        name: sp("Additive".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    trait_registry
        .register_trait(&trait_def, &record_registry)
        .unwrap();
    let impl_block = kea_ast::ImplBlock {
        trait_name: sp("Additive".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    trait_registry.register_trait_impl(&impl_block).unwrap();
    trait_registry.add_impl_methods(BTreeMap::new()).unwrap();

    // 2. Build the desugared form of `fn total(x) where x: Additive { x }`
    //    which is: `let total = |x| x`
    let expr = let_bind("total", lambda(&["x"], var("x")));

    // Also build the FnDecl for apply_where_clause (it needs param names + where_clause).
    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("total".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("x".to_string())),
            annotation: None,
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: var("x"),
        span: s(),
        where_clause: vec![TraitBound {
            type_var: sp("x".to_string()),
            trait_name: sp("Additive".to_string()),
        }],
        testing: None,
        testing_tags: Vec::new(),
    };

    // 3. Infer (mimics MCP type_check_decls flow)
    let mut env = TypeEnv::new();
    let mut unifier1 = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier1,
        &record_registry,
        &trait_registry,
        &SumTypeRegistry::new(),
    );
    assert!(
        !unifier1.has_errors(),
        "fn decl should type-check: {:?}",
        unifier1.errors()
    );

    // 4. Apply where-clause bounds to the scheme
    let scheme_before = env.lookup("total").cloned().unwrap();
    assert!(
        scheme_before.bounds.is_empty(),
        "bounds should be empty before apply_where_clause"
    );

    let mut scheme = scheme_before;
    apply_where_clause(&mut scheme, &fn_decl, &unifier1.substitution);
    assert!(
        !scheme.bounds.is_empty(),
        "bounds should be populated after apply_where_clause; \
         scheme.type_vars={:?}, scheme.ty={:?}",
        scheme.type_vars,
        scheme.ty
    );
    env.bind("total".to_string(), scheme);

    // 5. Now type-check `total("hello")` — should FAIL (String not Additive)
    let call_expr = call(var("total"), vec![lit_str("hello")]);
    let mut unifier2 = Unifier::new();
    let _result = infer_and_resolve(
        &call_expr,
        &mut env,
        &mut unifier2,
        &record_registry,
        &trait_registry,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier2.has_errors(), "unification itself should succeed");

    // 6. Check trait bounds — String doesn't implement Additive
    unifier2.check_trait_bounds(&trait_registry);
    assert!(
        unifier2.has_errors(),
        "String should NOT satisfy Additive; trait_bounds={:?}",
        unifier2.trait_bounds
    );
    assert!(
        unifier2.errors()[0].message.contains("String"),
        "error should mention String: {}",
        unifier2.errors()[0].message
    );

    // 7. Type-check `total(42)` — should PASS (Int implements Additive)
    let call_expr2 = call(var("total"), vec![lit_int(42)]);
    let mut unifier3 = Unifier::new();
    let _result = infer_and_resolve(
        &call_expr2,
        &mut env,
        &mut unifier3,
        &record_registry,
        &trait_registry,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier3.has_errors());
    unifier3.check_trait_bounds(&trait_registry);
    assert!(
        !unifier3.has_errors(),
        "Int should satisfy Additive: {:?}",
        unifier3.errors()
    );
}

// =========================================================================
// frame literal parsing
// =========================================================================

// ---------------------------------------------------------------------------
// Actor trait enforcement on spawn
// ---------------------------------------------------------------------------

/// Helper: register a named record + optionally impl Actor for it.
fn setup_actor_test(impl_actor: bool) -> (TypeEnv, RecordRegistry, TraitRegistry) {
    let mut records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();

    // Register Actor trait (built-in)
    let actor_trait = kea_ast::TraitDef {
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

    // Register `record Counter { count: Int }`
    let counter_def = make_record_def(
        "Counter",
        vec![("count", TypeAnnotation::Named("Int".to_string()))],
    );
    records.register(&counter_def).unwrap();
    traits.register_type_owner("Counter", "repl:");

    // Optionally register `impl Actor for Counter {}`
    if impl_actor {
        let impl_block = kea_ast::ImplBlock {
            trait_name: sp("Actor".to_string()),
            type_name: sp("Counter".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![],
        };
        traits.register_trait_impl(&impl_block).unwrap();
    }

    let mut env = TypeEnv::new();
    // Bind Counter as a constructor: Counter { count: Int }
    // For spawn tests, we bind a pre-typed variable instead.
    env.bind(
        "counter_val".into(),
        kea_types::TypeScheme::mono(Type::Record(kea_types::RecordType {
            name: "Counter".to_string(),
            params: vec![],
            row: kea_types::RowType::closed(vec![(Label::new("count"), Type::Int)]),
        })),
    );

    (env, records, traits)
}

#[test]
fn spawn_without_actor_impl_returns_task() {
    let (mut env, records, traits) = setup_actor_test(false);
    let expr = spawn_expr(var("counter_val"));
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        !unifier.has_errors(),
        "spawn without impl Actor should infer Task: {:?}",
        unifier.errors()
    );
    assert!(matches!(ty, Type::Task(_)), "expected Task(_), got {ty}");
}

#[test]
fn spawn_with_actor_impl_succeeds() {
    let (mut env, records, traits) = setup_actor_test(true);
    let expr = spawn_expr(var("counter_val"));
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        !unifier.has_errors(),
        "spawn with impl Actor should succeed: {:?}",
        unifier.errors()
    );
    assert!(
        matches!(ty, Type::Actor(_)),
        "result should be Actor type, got {ty}"
    );
}

#[test]
fn spawn_primitive_still_works() {
    // Spawn of a primitive type (Int) is permissive — generic dispatch
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let expr = spawn_expr(lit_int(42));
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        !unifier.has_errors(),
        "spawn Int should still work: {:?}",
        unifier.errors
    );
    assert!(matches!(ty, Type::Actor(ref inner) if **inner == Type::Int));
}

#[test]
fn spawn_still_checks_sendable_with_actor() {
    // Even with impl Actor, closure is still not Sendable
    let (mut env, records, traits) = setup_actor_test(true);
    // Override counter_val binding with a closure type to trigger Sendable error
    env.bind(
        "bad_val".into(),
        kea_types::TypeScheme::mono(Type::Function(kea_types::FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })),
    );
    let expr = spawn_expr(var("bad_val"));
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        unifier.has_errors(),
        "spawn of Function should still fail Sendable check"
    );
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("Sendable"),
        "error should mention Sendable, got: {msg}"
    );
}

#[test]
fn infer_await_requires_task() {
    let expr = await_expr(lit_int(1), false);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors(), "await on non-Task should error");
}

#[test]
fn infer_await_and_await_safe_types() {
    let expr = block(vec![
        let_bind("t", spawn_expr(lit_int(7))),
        sp(ExprKind::Tuple(vec![
            await_expr(var("t"), false),
            await_expr(var("t2"), true),
        ])),
    ]);
    let mut env = TypeEnv::new();
    env.bind(
        "t2".into(),
        TypeScheme::mono(Type::Task(Box::new(Type::Int))),
    );
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        !unifier.has_errors(),
        "await over Task should typecheck: {:?}",
        unifier.errors()
    );
    match ty {
        Type::Tuple(items) => {
            assert_eq!(items[0], Type::Int);
            assert_eq!(
                items[1],
                Type::Result(
                    Box::new(Type::Int),
                    Box::new(
                        kea_types::builtin_error_sum_type("ActorError")
                            .expect("builtin ActorError type"),
                    ),
                )
            );
        }
        other => panic!("expected tuple result, got {other}"),
    }
}

// ---------------------------------------------------------------------------
// Spawn config type checking
// ---------------------------------------------------------------------------

#[test]
fn spawn_config_mailbox_size_must_be_int() {
    let (mut env, records, traits) = setup_actor_test(true);
    let mut unifier = Unifier::new();
    let config = kea_ast::SpawnConfig {
        mailbox_size: Some(lit_str("not_int")),
        supervision: None,
        max_restarts: None,
        call_timeout: None,
    };
    let expr = sp(ExprKind::Spawn {
        value: Box::new(var("counter_val")),
        config: Some(Box::new(config)),
    });
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        unifier.has_errors(),
        "String mailbox_size should cause type error"
    );
}

#[test]
fn spawn_config_valid_int_succeeds() {
    let (mut env, records, traits) = setup_actor_test(true);
    let mut unifier = Unifier::new();
    let config = kea_ast::SpawnConfig {
        mailbox_size: Some(lit_int(100)),
        supervision: None,
        max_restarts: Some(lit_int(5)),
        call_timeout: None,
    };
    let expr = sp(ExprKind::Spawn {
        value: Box::new(var("counter_val")),
        config: Some(Box::new(config)),
    });
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors(), "errors: {:?}", unifier.errors());
    // Return type should still be Actor(Counter)
    assert!(matches!(ty, Type::Actor(_)));
}

#[test]
fn spawn_config_precision_int_types_succeed() {
    let (mut env, records, traits) = setup_actor_test(true);
    env.bind(
        "mailbox_i32".to_string(),
        kea_types::TypeScheme::mono(Type::IntN(
            kea_types::IntWidth::I32,
            kea_types::Signedness::Signed,
        )),
    );
    env.bind(
        "restarts_u16".to_string(),
        kea_types::TypeScheme::mono(Type::IntN(
            kea_types::IntWidth::I16,
            kea_types::Signedness::Unsigned,
        )),
    );
    env.bind(
        "timeout_i64".to_string(),
        kea_types::TypeScheme::mono(Type::IntN(
            kea_types::IntWidth::I64,
            kea_types::Signedness::Signed,
        )),
    );

    let mut unifier = Unifier::new();
    let config = kea_ast::SpawnConfig {
        mailbox_size: Some(var("mailbox_i32")),
        supervision: None,
        max_restarts: Some(var("restarts_u16")),
        call_timeout: Some(var("timeout_i64")),
    };
    let expr = sp(ExprKind::Spawn {
        value: Box::new(var("counter_val")),
        config: Some(Box::new(config)),
    });
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(
        !unifier.has_errors(),
        "precision integer config should be accepted: {:?}",
        unifier.errors()
    );
    assert!(matches!(ty, Type::Actor(_)));
}

#[test]
fn spawn_config_supervision_requires_supervision_action_sum_type() {
    let (mut env, records, traits) = setup_actor_test(true);
    let mut unifier = Unifier::new();
    let config = kea_ast::SpawnConfig {
        mailbox_size: None,
        supervision: Some(atom_expr("restart")),
        max_restarts: None,
        call_timeout: None,
    };
    let expr = sp(ExprKind::Spawn {
        value: Box::new(var("counter_val")),
        config: Some(Box::new(config)),
    });
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        unifier.has_errors(),
        "atom supervision value should fail (expected SupervisionAction)"
    );
}

#[test]
fn spawn_config_supervision_accepts_restart_constructor() {
    let (mut env, records, traits) = setup_actor_test(true);
    let mut unifier = Unifier::new();
    let config = kea_ast::SpawnConfig {
        mailbox_size: None,
        supervision: Some(constructor("Restart", vec![])),
        max_restarts: None,
        call_timeout: None,
    };
    let expr = sp(ExprKind::Spawn {
        value: Box::new(var("counter_val")),
        config: Some(Box::new(config)),
    });
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        !unifier.has_errors(),
        "Restart constructor should satisfy SupervisionAction: {:?}",
        unifier.errors()
    );
    assert!(matches!(ty, Type::Actor(_)));
}

// ---------------------------------------------------------------------------
// Dispatch semantics and actor protocol
// ---------------------------------------------------------------------------

#[test]
fn dispatch_semantics_self_return_is_send() {
    let counter = Type::Record(RecordType {
        name: "Counter".to_string(),
        params: vec![],
        row: RowType::closed(vec![(Label::new("count"), Type::Int)]),
    });
    assert_eq!(
        derive_dispatch_semantics("Counter", &counter),
        DispatchSemantics::Send,
    );
}

#[test]
fn dispatch_semantics_non_self_return_is_call() {
    assert_eq!(
        derive_dispatch_semantics("Counter", &Type::Int),
        DispatchSemantics::CallPure,
    );
}

#[test]
fn dispatch_semantics_tuple_self_return_is_call_with_state() {
    let counter = Type::Record(RecordType {
        name: "Counter".to_string(),
        params: vec![],
        row: RowType::closed(vec![(Label::new("count"), Type::Int)]),
    });
    let ret = Type::Tuple(vec![counter.clone(), Type::Int]);
    assert_eq!(
        derive_dispatch_semantics("Counter", &ret),
        DispatchSemantics::CallWithState,
    );
}

#[test]
fn dispatch_semantics_unresolved_var_defaults_to_call() {
    let var_ty = Type::Var(TypeVarId(999));
    assert_eq!(
        derive_dispatch_semantics("Counter", &var_ty),
        DispatchSemantics::CallPure,
    );
}

#[test]
fn build_protocol_strips_self_param() {
    let counter = Type::Record(RecordType {
        name: "Counter".to_string(),
        params: vec![],
        row: RowType::closed(vec![(Label::new("count"), Type::Int)]),
    });
    let mut methods = BTreeMap::new();
    // fn inc(self) -> Counter
    methods.insert(
        "inc".to_string(),
        Type::Function(FunctionType {
            params: vec![counter.clone()],
            ret: Box::new(counter.clone()),
            effects: EffectRow::pure(),
        }),
    );
    // fn get(self) -> Int
    methods.insert(
        "get".to_string(),
        Type::Function(FunctionType {
            params: vec![counter.clone()],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        }),
    );
    let protocol = build_actor_protocol("Counter", &methods, None);
    assert_eq!(protocol.type_name, "Counter");
    assert_eq!(protocol.methods.len(), 2);

    let inc = &protocol.methods["inc"];
    assert!(
        inc.params.is_empty(),
        "self should be stripped: {:?}",
        inc.params
    );
    assert_eq!(inc.semantics, DispatchSemantics::Send);

    let get = &protocol.methods["get"];
    assert!(
        get.params.is_empty(),
        "self should be stripped: {:?}",
        get.params
    );
    assert_eq!(get.semantics, DispatchSemantics::CallPure);
}

#[test]
fn register_and_find_protocol_roundtrip() {
    let counter = Type::Record(RecordType {
        name: "Counter".to_string(),
        params: vec![],
        row: RowType::closed(vec![(Label::new("count"), Type::Int)]),
    });
    let mut methods = BTreeMap::new();
    methods.insert(
        "inc".to_string(),
        Type::Function(FunctionType {
            params: vec![counter.clone()],
            ret: Box::new(counter),
            effects: EffectRow::pure(),
        }),
    );
    let protocol = build_actor_protocol("Counter", &methods, None);

    let mut traits = TraitRegistry::new();
    traits.register_actor_protocol(protocol);

    let found = traits.find_actor_protocol("Counter");
    assert!(found.is_some(), "protocol should be found");
    assert_eq!(found.unwrap().methods.len(), 1);
    assert!(traits.find_actor_protocol("Missing").is_none());
}

// ---------------------------------------------------------------------------
// Step 4: send/call type-checking with method resolution
// ---------------------------------------------------------------------------

/// Setup an actor with a full protocol: inc (Send), get (CallPure), get_and_update (CallWithState)
fn setup_actor_protocol_test() -> (TypeEnv, RecordRegistry, TraitRegistry) {
    let (mut env, records, mut traits) = setup_actor_test(true);

    let counter_ty = Type::Record(RecordType {
        name: "Counter".to_string(),
        params: vec![],
        row: RowType::closed(vec![(Label::new("count"), Type::Int)]),
    });

    let mut methods = BTreeMap::new();
    // inc(self) -> Counter  (Send — returns Self)
    methods.insert(
        "inc".to_string(),
        Type::Function(FunctionType {
            params: vec![counter_ty.clone()],
            ret: Box::new(counter_ty.clone()),
            effects: EffectRow::pure(),
        }),
    );
    // get(self) -> Int  (CallPure — returns non-Self)
    methods.insert(
        "get".to_string(),
        Type::Function(FunctionType {
            params: vec![counter_ty.clone()],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        }),
    );
    // get_and_update(self, Int) -> #(Counter, Int)  (CallWithState)
    methods.insert(
        "get_and_update".to_string(),
        Type::Function(FunctionType {
            params: vec![counter_ty.clone(), Type::Int],
            ret: Box::new(Type::Tuple(vec![counter_ty.clone(), Type::Int])),
            effects: EffectRow::pure(),
        }),
    );

    let protocol = build_actor_protocol("Counter", &methods, None);
    traits.register_actor_protocol(protocol);

    // Bind an Actor(Counter) value
    env.bind(
        "c".into(),
        kea_types::TypeScheme::mono(Type::Actor(Box::new(counter_ty))),
    );

    (env, records, traits)
}

#[test]
fn send_known_method_typechecks() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    let expr = actor_send(var("c"), "inc", vec![]);
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors(), "errors: {:?}", unifier.errors());
    assert_eq!(ty, Type::Unit);
}

#[test]
fn try_send_known_method_typechecks() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    let expr = actor_try_send(var("c"), "inc", vec![]);
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors(), "errors: {:?}", unifier.errors());
    assert_eq!(
        ty,
        Type::Result(
            Box::new(Type::Unit),
            Box::new(kea_types::builtin_error_sum_type("ActorError").expect("builtin error type"))
        )
    );
}

#[test]
fn send_unknown_method_is_error() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    let expr = actor_send(var("c"), "nonexistent", vec![]);
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors());
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("no method"),
        "expected 'no method' error, got: {msg}"
    );
}

#[test]
fn send_call_only_method_is_error() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    // `get` is CallPure, so send should error
    let expr = actor_send(var("c"), "get", vec![]);
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors());
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("use `call`"),
        "expected 'use call' error, got: {msg}"
    );
}

#[test]
fn try_send_call_only_method_is_error() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    let expr = actor_try_send(var("c"), "get", vec![]);
    let _ = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        unifier.has_errors(),
        "try_send on call-only method should produce an error"
    );
}

#[test]
fn call_on_send_method_returns_result_unit() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    // `call` on `inc` (Send) should return Unit directly
    let expr = actor_call(var("c"), "inc", vec![]);
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors(), "errors: {:?}", unifier.errors());
    assert_eq!(ty, Type::Unit);
}

#[test]
fn call_returns_result_of_method_return_type() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    // `call` on `get` (CallPure) should return Int directly
    let expr = actor_call(var("c"), "get", vec![]);
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors(), "errors: {:?}", unifier.errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn call_safe_returns_result_of_method_return_type() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    // `call?` on `get` (CallPure) should return Result(Int, ActorError)
    let expr = actor_call_safe(var("c"), "get", vec![]);
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors(), "errors: {:?}", unifier.errors());
    assert_eq!(
        ty,
        Type::Result(
            Box::new(Type::Int),
            Box::new(kea_types::builtin_error_sum_type("ActorError").expect("builtin error type"))
        )
    );
}

#[test]
fn call_arg_type_mismatch_is_error() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    // `get_and_update` expects (Int) but we pass (String)
    let expr = actor_call(var("c"), "get_and_update", vec![lit_str("oops")]);
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors(), "should have type mismatch error");
}

#[test]
fn call_arg_count_mismatch_is_error() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    // `get_and_update` expects 1 arg (Int), but we pass none
    let expr = actor_call(var("c"), "get_and_update", vec![]);
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors());
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("expects 1 argument"),
        "expected arg count error, got: {msg}"
    );
}

#[test]
fn call_with_state_returns_second_element() {
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    // `call` on `get_and_update` (CallWithState) should return Int
    // because #(Counter, Int) → extracts Int (second element)
    let expr = actor_call(var("c"), "get_and_update", vec![lit_int(42)]);
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors(), "errors: {:?}", unifier.errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn unresolved_actor_type_is_permissive() {
    // When actor type is unknown (just a type variable), send/call should still work
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    // Bind `a` as an unresolved type variable
    let var_ty = unifier.fresh_type();
    env.bind("a".into(), kea_types::TypeScheme::mono(var_ty));
    // send should succeed — permissive for unresolved types
    let expr = actor_send(var("a"), "anything", vec![]);
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    // Should not have protocol-related errors (may have other unification artifacts)
    let errors = unifier.errors();
    let has_protocol_error = errors.iter().any(|e| {
        let msg = format!("{e:?}");
        msg.contains("no method") || msg.contains("use `call`")
    });
    assert!(
        !has_protocol_error,
        "should not have protocol errors for unresolved type, got: {:?}",
        errors
    );
}

#[test]
fn send_with_correct_args_typechecks() {
    // Verify send passes args correctly (inc takes no extra args after self)
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    // inc takes no user args, passing one should error
    let expr = actor_send(var("c"), "inc", vec![lit_int(1)]);
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors());
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("expects 0 argument"),
        "expected arg count error, got: {msg}"
    );
}

// ---------------------------------------------------------------------------
// Fix 7: Protocol fallback → error for concrete types
// ---------------------------------------------------------------------------

#[test]
fn send_on_concrete_type_without_protocol_is_error() {
    // Counter has `impl Actor` but no protocol registered (no methods)
    let (mut env, records, traits) = setup_actor_test(true);
    let mut unifier = Unifier::new();

    // Bind `a` as Actor(Counter)
    let counter_ty = Type::Record(RecordType {
        name: "Counter".to_string(),
        params: vec![],
        row: RowType::closed(vec![(Label::new("count"), Type::Int)]),
    });
    env.bind(
        "a".into(),
        kea_types::TypeScheme::mono(Type::Actor(Box::new(counter_ty))),
    );

    let expr = actor_send(var("a"), "anything", vec![]);
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors());
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("no registered protocol"),
        "expected 'no registered protocol' error, got: {msg}"
    );
}

#[test]
fn call_on_concrete_type_without_protocol_is_error() {
    let (mut env, records, traits) = setup_actor_test(true);
    let mut unifier = Unifier::new();

    let counter_ty = Type::Record(RecordType {
        name: "Counter".to_string(),
        params: vec![],
        row: RowType::closed(vec![(Label::new("count"), Type::Int)]),
    });
    env.bind(
        "a".into(),
        kea_types::TypeScheme::mono(Type::Actor(Box::new(counter_ty))),
    );

    let expr = actor_call(var("a"), "anything", vec![]);
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors());
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("no registered protocol"),
        "expected 'no registered protocol' error, got: {msg}"
    );
}

// ---------------------------------------------------------------------------
// Atom expressions
// ---------------------------------------------------------------------------

fn atom_expr(name: &str) -> Expr {
    sp(ExprKind::Atom(name.to_string()))
}

#[test]
fn atom_has_atom_type() {
    let (ty, u) = infer(&atom_expr("foo"));
    assert!(!u.has_errors());
    assert_eq!(ty, Type::Atom);
}

#[test]
fn atom_different_names_same_type() {
    let (ty1, u1) = infer(&atom_expr("restart"));
    let (ty2, u2) = infer(&atom_expr("stop"));
    assert!(!u1.has_errors());
    assert!(!u2.has_errors());
    assert_eq!(ty1, Type::Atom);
    assert_eq!(ty2, Type::Atom);
    assert_eq!(ty1, ty2);
}

#[test]
fn atom_is_sendable() {
    assert!(is_sendable(&Type::Atom));
}

#[test]
fn atom_in_list_infers_list_atom() {
    // [: foo, :bar] should be List(Atom)
    let expr = sp(ExprKind::List(vec![atom_expr("foo"), atom_expr("bar")]));
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors());
    assert_eq!(ty, Type::List(Box::new(Type::Atom)));
}

#[test]
fn atom_display() {
    assert_eq!(Type::Atom.to_string(), "Atom");
}

fn dim_tags(entries: &[(&str, i64)]) -> BTreeMap<String, i64> {
    entries
        .iter()
        .map(|(k, v)| ((*k).to_string(), *v))
        .collect()
}

#[test]
fn tagged_types_unify_when_tags_match() {
    let tagged_a = Type::Tagged {
        inner: Box::new(Type::Float),
        tags: dim_tags(&[("length", 1)]),
    };
    let tagged_b = Type::Tagged {
        inner: Box::new(Type::Float),
        tags: dim_tags(&[("length", 1)]),
    };

    let mut unifier = Unifier::new();
    let prov = Provenance {
        span: s(),
        reason: Reason::LetAnnotation,
    };
    unifier.unify(&tagged_a, &tagged_b, &prov);
    assert!(!unifier.has_errors(), "errors: {:?}", unifier.errors());
}

#[test]
fn tagged_types_fail_when_tags_differ() {
    let tagged_a = Type::Tagged {
        inner: Box::new(Type::Float),
        tags: dim_tags(&[("length", 1)]),
    };
    let tagged_b = Type::Tagged {
        inner: Box::new(Type::Float),
        tags: dim_tags(&[("time", 1)]),
    };

    let mut unifier = Unifier::new();
    let prov = Provenance {
        span: s(),
        reason: Reason::LetAnnotation,
    };
    unifier.unify(&tagged_a, &tagged_b, &prov);
    assert!(unifier.has_errors(), "expected tag mismatch error");
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("incompatible dimensional tags"),
        "expected dimensional tag mismatch error, got: {msg}"
    );
}

#[test]
fn tagged_inner_type_unifies() {
    let tv = TypeVarId(42);
    let tagged_var = Type::Tagged {
        inner: Box::new(Type::Var(tv)),
        tags: dim_tags(&[("length", 1)]),
    };
    let tagged_float = Type::Tagged {
        inner: Box::new(Type::Float),
        tags: dim_tags(&[("length", 1)]),
    };

    let mut unifier = Unifier::new();
    let prov = Provenance {
        span: s(),
        reason: Reason::LetAnnotation,
    };
    unifier.unify(&tagged_var, &tagged_float, &prov);
    assert!(!unifier.has_errors(), "errors: {:?}", unifier.errors());
    assert_eq!(unifier.substitution.apply(&Type::Var(tv)), Type::Float);
}

#[test]
fn tagged_type_is_sendable() {
    let ty = Type::Tagged {
        inner: Box::new(Type::Int),
        tags: dim_tags(&[("length", 1)]),
    };
    assert!(is_sendable(&ty));
}

// ---------------------------------------------------------------------------
// actor_ref() type checking
// ---------------------------------------------------------------------------

#[test]
fn actor_ref_type_is_actor_self() {
    // Simulate: type-checking methods inside `impl Counter` where Counter has Actor trait.
    // actor_ref() should return Actor(Counter).
    let (mut env, records, traits) = setup_actor_test(true);
    // Bind actor_ref as () -> Actor(Counter) — same as main.rs does
    let record_ty = records.to_type("Counter").unwrap();
    env.bind(
        "actor_ref".into(),
        kea_types::TypeScheme::mono(Type::Function(kea_types::FunctionType {
            params: vec![],
            ret: Box::new(Type::Actor(Box::new(record_ty))),
            effects: EffectRow::pure(),
        })),
    );
    // actor_ref() is a zero-arg function call
    let expr = call(var("actor_ref"), vec![]);
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        !unifier.has_errors(),
        "actor_ref() should type-check: {:?}",
        unifier.errors()
    );
    assert!(
        matches!(ty, Type::Actor(ref inner) if matches!(&**inner, Type::Record(rt) if rt.name == "Counter")),
        "actor_ref() should return Actor(Counter), got {ty}"
    );
}

#[test]
fn actor_ref_outside_method_is_undefined() {
    // Without actor_ref in scope, it's an undefined variable
    let (mut env, records, traits) = setup_actor_test(true);
    // Don't bind actor_ref — simulating code outside actor methods
    let expr = call(var("actor_ref"), vec![]);
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        unifier.has_errors(),
        "actor_ref() outside actor method should error"
    );
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("actor_ref"),
        "error should mention actor_ref, got: {msg}"
    );
}

// ---------------------------------------------------------------------------
// concrete_method_types_from_decls
// ---------------------------------------------------------------------------

/// Helper to build a FnDecl with explicit Param list and optional return annotation.
/// Unlike the simpler `make_fn_decl`, this supports self params, annotations, etc.
fn make_method_decl(
    name: &str,
    params: Vec<Param>,
    return_annotation: Option<TypeAnnotation>,
    body: Expr,
) -> FnDecl {
    FnDecl {
        annotations: vec![],
        public: false,
        name: sp(name.to_string()),
        doc: None,
        params,
        return_annotation: return_annotation.map(sp),
        effect_annotation: None,
        body,
        span: s(),
        where_clause: vec![],
        testing: None,
        testing_tags: Vec::new(),
    }
}

fn self_param() -> Param {
    Param {
        label: ParamLabel::Implicit,
        pattern: sp(PatternKind::Var("self".to_string())),
        annotation: None,
        default: None,
    }
}

fn annotated_param(name: &str, ann: TypeAnnotation) -> Param {
    Param {
        label: ParamLabel::Implicit,
        pattern: sp(PatternKind::Var(name.to_string())),
        annotation: Some(sp(ann)),
        default: None,
    }
}

#[test]
fn concrete_method_types_self_return_resolves_to_record() {
    // fn inc(self) -> Self { self }
    // Should produce Function([Counter], Counter) — Self maps to Counter
    let mut records = RecordRegistry::new();
    let counter_def = make_record_def(
        "Counter",
        vec![("count", TypeAnnotation::Named("Int".to_string()))],
    );
    records.register(&counter_def).unwrap();

    let decl = make_method_decl(
        "inc",
        vec![self_param()],
        Some(TypeAnnotation::Named("Self".to_string())),
        var("self"),
    );

    let result = concrete_method_types_from_decls("Counter", &[decl], &records);
    assert_eq!(result.len(), 1);
    let inc_ty = &result["inc"];
    if let Type::Function(ft) = inc_ty {
        // Return type should be the concrete Counter record, not Unit
        assert!(
            matches!(&*ft.ret, Type::Record(rt) if rt.name == "Counter"),
            "expected return type Record(Counter), got {:?}",
            ft.ret
        );
        // First param should be Counter (self)
        assert_eq!(ft.params.len(), 1);
        assert!(
            matches!(&ft.params[0], Type::Record(rt) if rt.name == "Counter"),
            "expected self param Record(Counter), got {:?}",
            ft.params[0]
        );
    } else {
        panic!("expected Function type, got {inc_ty:?}");
    }
}

#[test]
fn concrete_method_types_no_return_annotation_defaults_to_unit() {
    // fn fire(self) { } — no return annotation
    let mut records = RecordRegistry::new();
    let counter_def = make_record_def(
        "Counter",
        vec![("count", TypeAnnotation::Named("Int".to_string()))],
    );
    records.register(&counter_def).unwrap();

    let decl = make_method_decl("fire", vec![self_param()], None, lit_unit());

    let result = concrete_method_types_from_decls("Counter", &[decl], &records);
    assert_eq!(result.len(), 1);
    let fire_ty = &result["fire"];
    if let Type::Function(ft) = fire_ty {
        assert_eq!(
            *ft.ret,
            Type::Unit,
            "method with no return annotation should default to Unit"
        );
    } else {
        panic!("expected Function type, got {fire_ty:?}");
    }
}

#[test]
fn concrete_method_types_unknown_annotation_resolves_to_dynamic() {
    // fn foo(self, x: UnknownThing) -> Int
    // `UnknownThing` is not registered, so resolve_annotation returns None → Dynamic
    let mut records = RecordRegistry::new();
    let counter_def = make_record_def(
        "Counter",
        vec![("count", TypeAnnotation::Named("Int".to_string()))],
    );
    records.register(&counter_def).unwrap();

    let decl = make_method_decl(
        "foo",
        vec![
            self_param(),
            annotated_param("x", TypeAnnotation::Named("UnknownThing".to_string())),
        ],
        Some(TypeAnnotation::Named("Int".to_string())),
        lit_int(0),
    );

    let result = concrete_method_types_from_decls("Counter", &[decl], &records);
    assert_eq!(result.len(), 1);
    let foo_ty = &result["foo"];
    if let Type::Function(ft) = foo_ty {
        assert_eq!(ft.params.len(), 2, "should have self + x params");
        // First param is self → Counter
        assert!(
            matches!(&ft.params[0], Type::Record(rt) if rt.name == "Counter"),
            "expected self param Record(Counter), got {:?}",
            ft.params[0]
        );
        // Second param is x: UnknownThing → Dynamic
        assert_eq!(
            ft.params[1],
            Type::Dynamic,
            "unknown annotation should resolve to Dynamic"
        );
        // Return type is Int
        assert_eq!(*ft.ret, Type::Int);
    } else {
        panic!("expected Function type, got {foo_ty:?}");
    }
}

// ---------------------------------------------------------------------------
// send on CallWithState method should be an error
// ---------------------------------------------------------------------------

#[test]
fn send_call_with_state_method_is_error() {
    // send on a CallWithState method should produce an error
    // (send is only valid for Send methods)
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    // `get_and_update` is CallWithState (returns #(Counter, Int)),
    // so send should produce "returns a value — use `call`" error
    let expr = actor_send(var("c"), "get_and_update", vec![lit_int(1)]);
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors());
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("use `call`"),
        "expected 'use call' error for CallWithState method, got: {msg}"
    );
}

// ---------------------------------------------------------------------------
// spawn record with closure field fails Sendable check
// ---------------------------------------------------------------------------

#[test]
fn spawn_record_with_closure_field_not_sendable() {
    // record Handler { callback: (Int) -> Int }
    // spawn Handler { callback: |x| x }
    // Should fail Sendable check on the record's fields
    let mut records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();

    // Register Actor trait
    let actor_trait = kea_ast::TraitDef {
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

    // Register `record Handler { callback: (Int) -> Int }` — we use the AST def
    // for registration but the record row manually with Function type.
    // RecordDef needs TypeAnnotation, but RecordRegistry stores the resolved row.
    // The key fact is that the record HAS a Function-typed field.
    let handler_def = make_record_def(
        "Handler",
        vec![(
            "callback",
            TypeAnnotation::Function(
                vec![TypeAnnotation::Named("Int".to_string())],
                Box::new(TypeAnnotation::Named("Int".to_string())),
            ),
        )],
    );
    records.register(&handler_def).unwrap();
    traits.register_type_owner("Handler", "repl:");

    // Register `impl Actor for Handler {}`
    let impl_block = kea_ast::ImplBlock {
        trait_name: sp("Actor".to_string()),
        type_name: sp("Handler".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    traits.register_trait_impl(&impl_block).unwrap();

    // Build the Handler value with a Function-typed field
    let handler_ty = Type::Record(RecordType {
        name: "Handler".to_string(),
        params: vec![],
        row: RowType::closed(vec![(
            Label::new("callback"),
            Type::Function(FunctionType {
                params: vec![Type::Int],
                ret: Box::new(Type::Int),
                effects: EffectRow::pure(),
            }),
        )]),
    });

    let mut env = TypeEnv::new();
    env.bind("h".into(), kea_types::TypeScheme::mono(handler_ty));

    let expr = spawn_expr(var("h"));
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        unifier.has_errors(),
        "spawn of record with Function field should fail Sendable check"
    );
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("Sendable"),
        "error should mention Sendable, got: {msg}"
    );
}

// ---------------------------------------------------------------------------
// Associated types
// ---------------------------------------------------------------------------

#[test]
fn trait_with_associated_type_stored() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![make_trait_method(
            "from",
            vec![(
                "value",
                Some(TypeAnnotation::Projection {
                    base: "Self".into(),
                    name: "Source".into(),
                }),
            )],
            Some(TypeAnnotation::Named("Self".into())),
        )],
    };
    traits.register_trait(&def, &records).unwrap();
    let info = traits.lookup_trait("From").unwrap();
    assert_eq!(info.associated_types.len(), 1);
    assert_eq!(info.associated_types[0].name, "Source");
}

#[test]
fn impl_with_associated_type_coherence_allows_different() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    // First impl: From for Int where Source = String
    let block1 = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    traits.register_trait_impl(&block1).unwrap();

    // Second impl: From for Int where Source = Float — should succeed
    let block2 = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("Float".into())),
        }],
    };
    assert!(traits.register_trait_impl(&block2).is_ok());

    // Third impl: From for Int where Source = String — duplicate, should fail
    let block3 = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    assert!(traits.register_trait_impl(&block3).is_err());
}

#[test]
fn impl_with_unknown_associated_type_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Item".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("Container".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Nope".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    let err = traits.register_trait_impl(&block).unwrap_err();
    assert!(err.message.contains("has no associated type `Nope`"));
}

#[test]
fn impl_with_duplicate_associated_type_assignment_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Item".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("Container".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![
            kea_ast::WhereItem::TypeAssignment {
                name: sp("Item".to_string()),
                ty: sp(TypeAnnotation::Named("String".into())),
            },
            kea_ast::WhereItem::TypeAssignment {
                name: sp("Item".to_string()),
                ty: sp(TypeAnnotation::Named("Bool".into())),
            },
        ],
    };
    let err = traits.register_trait_impl(&block).unwrap_err();
    assert!(
        err.message
            .contains("duplicate associated type assignment `Item`")
    );
}

#[test]
fn impl_missing_required_associated_type_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Item".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("Container".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    let err = traits.register_trait_impl(&block).unwrap_err();
    assert!(
        err.message
            .contains("missing associated type assignment `Item`")
    );
}

#[test]
fn impl_missing_associated_type_uses_trait_default() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Item".to_string()),
            constraints: vec![],
            default: Some(sp(TypeAnnotation::Named("String".into()))),
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("Container".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    traits.register_trait_impl(&block).unwrap();
    let outcome = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "Container".to_string(),
        base_ty: Type::Int,
        assoc: "Item".to_string(),
        rhs: Type::String,
    });
    assert!(matches!(outcome, SolveOutcome::Unique(_)));
}

#[test]
fn impl_default_associated_type_can_project_self_assoc() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![
            kea_ast::AssociatedTypeDecl {
                name: sp("Item".to_string()),
                constraints: vec![],
                default: None,
            },
            kea_ast::AssociatedTypeDecl {
                name: sp("Wrapped".to_string()),
                constraints: vec![],
                default: Some(sp(TypeAnnotation::Applied(
                    "Option".into(),
                    vec![TypeAnnotation::Projection {
                        base: "Self".into(),
                        name: "Item".into(),
                    }],
                ))),
            },
        ],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("Container".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Item".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    traits.register_trait_impl(&block).unwrap();

    let outcome = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "Container".to_string(),
        base_ty: Type::Int,
        assoc: "Wrapped".to_string(),
        rhs: Type::Option(Box::new(Type::String)),
    });
    assert!(matches!(outcome, SolveOutcome::Unique(_)));
}

#[test]
fn impl_associated_type_defaults_resolve_in_fixpoint_order() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![
            kea_ast::AssociatedTypeDecl {
                name: sp("Wrapped".to_string()),
                constraints: vec![],
                default: Some(sp(TypeAnnotation::Applied(
                    "Option".into(),
                    vec![TypeAnnotation::Projection {
                        base: "Self".into(),
                        name: "Item".into(),
                    }],
                ))),
            },
            kea_ast::AssociatedTypeDecl {
                name: sp("Item".to_string()),
                constraints: vec![],
                default: Some(sp(TypeAnnotation::Named("String".into()))),
            },
        ],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("Container".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![],
    };
    traits.register_trait_impl(&block).unwrap();

    let item_outcome = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "Container".to_string(),
        base_ty: Type::Int,
        assoc: "Item".to_string(),
        rhs: Type::String,
    });
    assert!(matches!(item_outcome, SolveOutcome::Unique(_)));

    let wrapped_outcome = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "Container".to_string(),
        base_ty: Type::Int,
        assoc: "Wrapped".to_string(),
        rhs: Type::Option(Box::new(Type::String)),
    });
    assert!(matches!(wrapped_outcome, SolveOutcome::Unique(_)));
}

#[test]
fn impl_explicit_associated_type_overrides_trait_default() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Item".to_string()),
            constraints: vec![],
            default: Some(sp(TypeAnnotation::Named("String".into()))),
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("Container".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Item".to_string()),
            ty: sp(TypeAnnotation::Named("Float".into())),
        }],
    };
    traits.register_trait_impl(&block).unwrap();
    let outcome = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "Container".to_string(),
        base_ty: Type::Int,
        assoc: "Item".to_string(),
        rhs: Type::Float,
    });
    assert!(matches!(outcome, SolveOutcome::Unique(_)));
}

#[test]
fn impl_explicit_associated_type_projection_is_order_invariant() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![
            kea_ast::AssociatedTypeDecl {
                name: sp("Item".to_string()),
                constraints: vec![],
                default: None,
            },
            kea_ast::AssociatedTypeDecl {
                name: sp("Wrapped".to_string()),
                constraints: vec![],
                default: None,
            },
        ],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("Container".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        // `Wrapped` appears before `Item` on purpose.
        where_clause: vec![
            kea_ast::WhereItem::TypeAssignment {
                name: sp("Wrapped".to_string()),
                ty: sp(TypeAnnotation::Applied(
                    "Option".into(),
                    vec![TypeAnnotation::Projection {
                        base: "Self".into(),
                        name: "Item".into(),
                    }],
                )),
            },
            kea_ast::WhereItem::TypeAssignment {
                name: sp("Item".to_string()),
                ty: sp(TypeAnnotation::Named("String".into())),
            },
        ],
    };
    traits.register_trait_impl(&block).unwrap();

    let wrapped = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "Container".to_string(),
        base_ty: Type::Int,
        assoc: "Wrapped".to_string(),
        rhs: Type::Option(Box::new(Type::String)),
    });
    assert!(matches!(wrapped, SolveOutcome::Unique(_)));
}

#[test]
fn trait_default_projection_unknown_assoc_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Wrapped".to_string()),
            constraints: vec![],
            default: Some(sp(TypeAnnotation::Applied(
                "Option".into(),
                vec![TypeAnnotation::Projection {
                    base: "Self".into(),
                    name: "Missing".into(),
                }],
            ))),
        }],
        methods: vec![],
    };
    let err = traits.register_trait(&def, &records).unwrap_err();
    assert!(
        err.message
            .contains("unknown associated type `Missing` referenced in `associated type default`")
    );
}

#[test]
fn impl_assignment_projection_unknown_assoc_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Container".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![
            kea_ast::AssociatedTypeDecl {
                name: sp("Item".to_string()),
                constraints: vec![],
                default: None,
            },
            kea_ast::AssociatedTypeDecl {
                name: sp("Wrapped".to_string()),
                constraints: vec![],
                default: None,
            },
        ],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("Container".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![
            kea_ast::WhereItem::TypeAssignment {
                name: sp("Item".to_string()),
                ty: sp(TypeAnnotation::Named("String".into())),
            },
            kea_ast::WhereItem::TypeAssignment {
                name: sp("Wrapped".to_string()),
                ty: sp(TypeAnnotation::Applied(
                    "Option".into(),
                    vec![TypeAnnotation::Projection {
                        base: "Self".into(),
                        name: "Missing".into(),
                    }],
                )),
            },
        ],
    };
    let err = traits.register_trait_impl(&block).unwrap_err();
    assert!(
        err.message.contains(
            "unknown associated type `Missing` referenced in `associated type assignment`"
        )
    );
}

#[test]
fn trait_fundep_unknown_symbol_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Convert".to_string()),
        doc: None,
        type_params: vec![kea_ast::TraitTypeParam {
            name: sp("C".to_string()),
            kind: KindAnnotation::Star,
        }],
        supertraits: vec![],
        fundeps: vec![kea_ast::FunctionalDependencyDecl {
            from: vec![sp("C".to_string())],
            to: vec![sp("Missing".to_string())],
        }],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    let err = traits.register_trait(&def, &records).unwrap_err();
    assert!(
        err.message
            .contains("functional dependency references unknown parameter or associated type")
    );
}

#[test]
fn trait_fundep_cycle_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Convert".to_string()),
        doc: None,
        type_params: vec![kea_ast::TraitTypeParam {
            name: sp("C".to_string()),
            kind: KindAnnotation::Star,
        }],
        supertraits: vec![],
        fundeps: vec![kea_ast::FunctionalDependencyDecl {
            from: vec![sp("C".to_string())],
            to: vec![sp("C".to_string())],
        }],
        associated_types: vec![],
        methods: vec![],
    };
    let err = traits.register_trait(&def, &records).unwrap_err();
    assert!(err.message.contains("is cyclic"));
}

#[test]
fn trait_fundep_duplicate_declaration_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Convert".to_string()),
        doc: None,
        type_params: vec![
            kea_ast::TraitTypeParam {
                name: sp("A".to_string()),
                kind: KindAnnotation::Star,
            },
            kea_ast::TraitTypeParam {
                name: sp("B".to_string()),
                kind: KindAnnotation::Star,
            },
        ],
        supertraits: vec![],
        fundeps: vec![
            kea_ast::FunctionalDependencyDecl {
                from: vec![sp("A".to_string())],
                to: vec![sp("B".to_string())],
            },
            kea_ast::FunctionalDependencyDecl {
                from: vec![sp("A".to_string())],
                to: vec![sp("B".to_string())],
            },
        ],
        associated_types: vec![],
        methods: vec![],
    };
    let err = traits.register_trait(&def, &records).unwrap_err();
    assert!(err.message.contains("duplicate functional dependency"));
}

#[test]
fn trait_fundep_duplicate_symbol_on_side_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Convert".to_string()),
        doc: None,
        type_params: vec![
            kea_ast::TraitTypeParam {
                name: sp("A".to_string()),
                kind: KindAnnotation::Star,
            },
            kea_ast::TraitTypeParam {
                name: sp("B".to_string()),
                kind: KindAnnotation::Star,
            },
        ],
        supertraits: vec![],
        fundeps: vec![kea_ast::FunctionalDependencyDecl {
            from: vec![sp("A".to_string()), sp("A".to_string())],
            to: vec![sp("B".to_string())],
        }],
        associated_types: vec![],
        methods: vec![],
    };
    let err = traits.register_trait(&def, &records).unwrap_err();
    assert!(err.message.contains("duplicate parameter `A`"));
}

#[test]
fn impl_with_fundep_conflicting_dependent_value_errors() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![kea_ast::TraitTypeParam {
            name: sp("T".to_string()),
            kind: KindAnnotation::Star,
        }],
        supertraits: vec![],
        fundeps: vec![kea_ast::FunctionalDependencyDecl {
            from: vec![sp("T".to_string())],
            to: vec![sp("Source".to_string())],
        }],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let first = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    traits.register_trait_impl(&first).unwrap();

    let second = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("Float".into())),
        }],
    };
    let err = traits.register_trait_impl(&second).unwrap_err();
    assert!(err.message.contains("functional dependency conflict"));
}

#[test]
fn impl_with_fundep_conflict_is_detected_across_different_type_names() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Convert".to_string()),
        doc: None,
        type_params: vec![kea_ast::TraitTypeParam {
            name: sp("C".to_string()),
            kind: KindAnnotation::Star,
        }],
        supertraits: vec![],
        fundeps: vec![kea_ast::FunctionalDependencyDecl {
            from: vec![sp("Source".to_string())],
            to: vec![sp("C".to_string())],
        }],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let first = kea_ast::ImplBlock {
        trait_name: sp("Convert".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    traits.register_trait_impl(&first).unwrap();

    let second = kea_ast::ImplBlock {
        trait_name: sp("Convert".to_string()),
        type_name: sp("Float".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    let err = traits.register_trait_impl(&second).unwrap_err();
    assert!(
        err.message.contains("functional dependency conflict"),
        "expected cross-type fundep conflict, got: {}",
        err.message
    );
}

#[test]
fn find_impl_with_assoc_selects_correct() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block1 = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    traits.register_trait_impl(&block1).unwrap();

    let block2 = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("Float".into())),
        }],
    };
    traits.register_trait_impl(&block2).unwrap();

    let ambiguous = traits.solve_goal(&TraitGoal::Implements {
        trait_name: "From".to_string(),
        ty: Type::Int,
    });
    assert!(matches!(ambiguous, SolveOutcome::Ambiguous(_)));

    // ProjectionEq disambiguates the associated type.
    let disambiguated = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "From".to_string(),
        base_ty: Type::Int,
        assoc: "Source".to_string(),
        rhs: Type::Float,
    });
    assert!(matches!(disambiguated, SolveOutcome::Unique(_)));
}

#[test]
fn solve_goal_implements_unknown_trait_reports_nomatch() {
    let traits = TraitRegistry::new();
    let outcome = traits.solve_goal(&TraitGoal::Implements {
        trait_name: "Show".to_string(),
        ty: Type::Int,
    });
    assert!(matches!(
        outcome,
        SolveOutcome::NoMatch(reasons)
            if reasons
                .iter()
                .any(|r| matches!(r, MismatchReason::UnknownTrait { trait_name } if trait_name == "Show"))
    ));
}

#[test]
fn solve_goal_implements_yields_unique_candidate() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Show", vec![]), &records)
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block("Show", "Int", vec![]))
        .unwrap();

    let outcome = traits.solve_goal(&TraitGoal::Implements {
        trait_name: "Show".to_string(),
        ty: Type::Int,
    });
    assert!(matches!(
        outcome,
        SolveOutcome::Unique(SolvedCandidate {
            trait_name,
            type_name,
            impl_index: Some(_),
            ..
        }) if trait_name == "Show" && type_name == "Int"
    ));
}

#[test]
fn solve_goal_implements_reports_ambiguous_candidates() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block1 = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    traits.register_trait_impl(&block1).unwrap();

    let block2 = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("Float".into())),
        }],
    };
    traits.register_trait_impl(&block2).unwrap();

    let outcome = traits.solve_goal(&TraitGoal::Implements {
        trait_name: "From".to_string(),
        ty: Type::Int,
    });

    assert!(matches!(
        outcome,
        SolveOutcome::Ambiguous(candidates) if candidates.len() == 2
    ));
}

#[test]
fn solve_goal_reports_ambiguous_param_bound_reason() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();

    let from_trait = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&from_trait, &records).unwrap();

    for source in ["String", "Float"] {
        let block = kea_ast::ImplBlock {
            trait_name: sp("From".to_string()),
            type_name: sp("Int".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![kea_ast::WhereItem::TypeAssignment {
                name: sp("Source".to_string()),
                ty: sp(TypeAnnotation::Named(source.to_string())),
            }],
        };
        traits.register_trait_impl(&block).unwrap();
    }

    traits
        .register_trait(&make_trait_def("Wrap", vec![]), &records)
        .unwrap();
    let wrap_impl = make_impl_block_with_params(
        "Wrap",
        "List",
        vec!["t"],
        vec![kea_ast::WhereItem::TraitBound(kea_ast::TraitBound {
            type_var: sp("t".to_string()),
            trait_name: sp("From".to_string()),
        })],
        vec![],
    );
    traits.register_trait_impl(&wrap_impl).unwrap();

    let outcome = traits.solve_goal(&TraitGoal::Implements {
        trait_name: "Wrap".to_string(),
        ty: Type::List(Box::new(Type::Int)),
    });
    assert!(matches!(
        outcome,
        SolveOutcome::NoMatch(reasons)
            if reasons.iter().any(|r| matches!(
                r,
                MismatchReason::ParamBoundAmbiguous { param, bound_trait, ty }
                    if param == "t" && bound_trait == "From" && ty == &Type::Int
            ))
    ));
}

#[test]
fn solve_goal_reports_ambiguous_supertrait_reason() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();

    let from_trait = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&from_trait, &records).unwrap();

    for source in ["String", "Float"] {
        let block = kea_ast::ImplBlock {
            trait_name: sp("From".to_string()),
            type_name: sp("Int".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![kea_ast::WhereItem::TypeAssignment {
                name: sp("Source".to_string()),
                ty: sp(TypeAnnotation::Named(source.to_string())),
            }],
        };
        traits.register_trait_impl(&block).unwrap();
    }

    let convert_trait = kea_ast::TraitDef {
        public: false,
        name: sp("Convert".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![sp("From".to_string())],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![],
    };
    traits.register_trait(&convert_trait, &records).unwrap();
    traits
        .register_trait_impl(&make_impl_block("Convert", "Int", vec![]))
        .unwrap();

    let outcome = traits.solve_goal(&TraitGoal::Implements {
        trait_name: "Convert".to_string(),
        ty: Type::Int,
    });
    assert!(matches!(
        outcome,
        SolveOutcome::NoMatch(reasons)
            if reasons.iter().any(|r| matches!(
                r,
                MismatchReason::SupertraitAmbiguous { supertrait, ty }
                    if supertrait == "From" && ty == &Type::Int
            ))
    ));
}

#[test]
fn resolve_resource_value_type_reports_ambiguous_impls() {
    let records = RecordRegistry::new();
    let sum_types = SumTypeRegistry::new();
    let mut env = TypeEnv::new();
    let mut unifier = Unifier::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let def = kea_ast::TraitDef {
        public: false,
        name: sp("Resource".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Value".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let mk_impl = |value_ty: TypeAnnotation| kea_ast::ImplBlock {
        trait_name: sp("Resource".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Value".to_string()),
            ty: sp(value_ty),
        }],
    };
    traits
        .register_trait_impl(&mk_impl(TypeAnnotation::Named("String".into())))
        .unwrap();
    traits
        .register_trait_impl(&mk_impl(TypeAnnotation::Named("Float".into())))
        .unwrap();

    let expr = block(vec![
        use_expr(Some(sp(PatternKind::Var("x".to_string()))), lit_int(1)),
        var("x"),
    ]);
    let _ = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sum_types);

    assert!(unifier.has_errors());
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message == "ambiguous impl resolution for trait `Resource` on type `Int`"),
        "expected ambiguity diagnostic, got {:?}",
        unifier
            .errors()
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );
}

#[test]
fn satisfies_type_rejects_ambiguity() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    for source in ["String", "Float"] {
        let block = kea_ast::ImplBlock {
            trait_name: sp("From".to_string()),
            type_name: sp("Int".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![kea_ast::WhereItem::TypeAssignment {
                name: sp("Source".to_string()),
                ty: sp(TypeAnnotation::Named(source.to_string())),
            }],
        };
        traits.register_trait_impl(&block).unwrap();
    }

    assert!(!has_unique_impl(&traits, "From", Type::Int));
}

#[test]
fn solve_goal_implements_reports_ambiguity_without_fallback_lookup() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let first = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    traits.register_trait_impl(&first).unwrap();

    let second = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("Float".into())),
        }],
    };
    traits.register_trait_impl(&second).unwrap();

    let outcome = traits.solve_goal(&TraitGoal::Implements {
        trait_name: "From".to_string(),
        ty: Type::Int,
    });
    assert!(
        matches!(outcome, SolveOutcome::Ambiguous(_)),
        "ambiguous lookup should not silently choose an impl"
    );
}

#[test]
fn solve_goal_projection_eq_disambiguates_associated_type() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    for source in ["String", "Float"] {
        let block = kea_ast::ImplBlock {
            trait_name: sp("From".to_string()),
            type_name: sp("Int".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![kea_ast::WhereItem::TypeAssignment {
                name: sp("Source".to_string()),
                ty: sp(TypeAnnotation::Named(source.to_string())),
            }],
        };
        traits.register_trait_impl(&block).unwrap();
    }

    let outcome = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "From".to_string(),
        base_ty: Type::Int,
        assoc: "Source".to_string(),
        rhs: Type::Float,
    });

    assert!(matches!(
        outcome,
        SolveOutcome::Unique(SolvedCandidate { associated_types, .. })
            if associated_types.get("Source") == Some(&Type::Float)
    ));
}

#[test]
fn solve_goal_projection_eq_reports_assoc_mismatch() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    traits.register_trait_impl(&block).unwrap();

    let outcome = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "From".to_string(),
        base_ty: Type::Int,
        assoc: "Source".to_string(),
        rhs: Type::Bool,
    });

    assert!(matches!(
        outcome,
        SolveOutcome::NoMatch(reasons)
            if reasons.iter().any(|r| matches!(
                r,
                MismatchReason::AssocTypeMismatch { assoc, expected, found }
                    if assoc == "Source" && expected == &Type::Bool && found == &Type::String
            ))
    ));
}

#[test]
fn solve_goal_projection_eq_accepts_variable_rhs_for_unique_candidate() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    let block = kea_ast::ImplBlock {
        trait_name: sp("From".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![],
        control_type: None,
        where_clause: vec![kea_ast::WhereItem::TypeAssignment {
            name: sp("Source".to_string()),
            ty: sp(TypeAnnotation::Named("String".into())),
        }],
    };
    traits.register_trait_impl(&block).unwrap();

    let outcome = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "From".to_string(),
        base_ty: Type::Int,
        assoc: "Source".to_string(),
        rhs: Type::Var(TypeVarId(0)),
    });

    assert!(matches!(
        outcome,
        SolveOutcome::Unique(SolvedCandidate { associated_types, .. })
            if associated_types.get("Source") == Some(&Type::String)
    ));
}

#[test]
fn solve_goal_projection_eq_variable_rhs_preserves_ambiguity() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![],
    };
    traits.register_trait(&def, &records).unwrap();

    for source in ["String", "Float"] {
        let block = kea_ast::ImplBlock {
            trait_name: sp("From".to_string()),
            type_name: sp("Int".to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![kea_ast::WhereItem::TypeAssignment {
                name: sp("Source".to_string()),
                ty: sp(TypeAnnotation::Named(source.into())),
            }],
        };
        traits.register_trait_impl(&block).unwrap();
    }

    let outcome = traits.solve_goal(&TraitGoal::ProjectionEq {
        base_trait: "From".to_string(),
        base_ty: Type::Int,
        assoc: "Source".to_string(),
        rhs: Type::Var(TypeVarId(0)),
    });

    assert!(
        matches!(outcome, SolveOutcome::Ambiguous(_)),
        "variable rhs should not collapse genuinely ambiguous projection candidates"
    );
}

#[test]
fn trait_method_self_projection_gets_placeholder() {
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    let def = kea_ast::TraitDef {
        public: false,
        name: sp("From".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![kea_ast::AssociatedTypeDecl {
            name: sp("Source".to_string()),
            constraints: vec![],
            default: None,
        }],
        methods: vec![make_trait_method(
            "from",
            vec![(
                "value",
                Some(TypeAnnotation::Projection {
                    base: "Self".into(),
                    name: "Source".into(),
                }),
            )],
            Some(TypeAnnotation::Named("Self".into())),
        )],
    };
    traits.register_trait(&def, &records).unwrap();
    let info = traits.lookup_trait("From").unwrap();
    let from_method = &info.methods[0];
    assert_eq!(from_method.param_types.len(), 1);
    // Self.Source should get a placeholder type variable, not fail
    assert!(matches!(from_method.param_types[0], Type::Var(_)));
}

#[test]
fn validate_fn_decl_annotations_reports_missing_parameter_annotations() {
    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("process".to_string()),
        doc: None,
        params: vec![
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("data".to_string())),
                annotation: None,
                default: None,
            },
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("threshold".to_string())),
                annotation: None,
                default: None,
            },
        ],
        return_annotation: None,
        effect_annotation: None,
        body: var("data"),
        span: s(),
        where_clause: vec![],
        testing: None,
        testing_tags: Vec::new(),
    };

    let diags = validate_fn_decl_annotations(&fn_decl);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].category, kea_diag::Category::MissingAnnotation);
    assert_eq!(diags[0].message, "missing type annotations on parameters");
    assert_eq!(diags[0].labels.len(), 2);
}

#[test]
fn validate_fn_decl_annotations_public_requires_return_annotation() {
    let fn_decl = FnDecl {
        annotations: vec![],
        public: true,
        name: sp("validate".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("value".to_string())),
            annotation: Some(sp(TypeAnnotation::Named("Int".to_string()))),
            default: None,
        }],
        return_annotation: None,
        effect_annotation: None,
        body: var("value"),
        span: s(),
        where_clause: vec![],
        testing: None,
        testing_tags: Vec::new(),
    };

    let diags = validate_fn_decl_annotations(&fn_decl);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].category, kea_diag::Category::MissingAnnotation);
    assert_eq!(diags[0].message, "public function missing return type");
}

#[test]
fn validate_fn_decl_annotations_allows_effect_var_in_function_type_annotation() {
    let fn_decl = FnDecl {
        annotations: vec![],
        public: false,
        name: sp("apply".to_string()),
        doc: None,
        params: vec![Param {
            label: ParamLabel::Implicit,
            pattern: sp(PatternKind::Var("f".to_string())),
            annotation: Some(sp(TypeAnnotation::FunctionWithEffect(
                vec![TypeAnnotation::Named("Int".to_string())],
                sp(EffectAnnotation::Var("e".to_string())),
                Box::new(TypeAnnotation::Named("Int".to_string())),
            ))),
            default: None,
        }],
        return_annotation: Some(sp(TypeAnnotation::Named("Int".to_string()))),
        effect_annotation: None,
        body: lit_int(1),
        span: s(),
        where_clause: vec![],
        testing: None,
        testing_tags: Vec::new(),
    };

    let diags = validate_fn_decl_annotations(&fn_decl);
    assert!(diags.is_empty());
}

#[test]
fn validate_trait_method_annotations_allow_effect_var_in_function_type_annotation() {
    let method = TraitMethod {
        name: sp("run".to_string()),
        params: vec![
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("self".to_string())),
                annotation: None,
                default: None,
            },
            Param {
                label: ParamLabel::Implicit,
                pattern: sp(PatternKind::Var("f".to_string())),
                annotation: Some(sp(TypeAnnotation::FunctionWithEffect(
                    vec![TypeAnnotation::Named("Int".to_string())],
                    sp(EffectAnnotation::Var("e".to_string())),
                    Box::new(TypeAnnotation::Named("Int".to_string())),
                ))),
                default: None,
            },
        ],
        return_annotation: Some(sp(TypeAnnotation::Named("Int".to_string()))),
        effect_annotation: None,
        where_clause: vec![],
        default_body: None,
        doc: None,
        span: s(),
    };

    let diags = validate_trait_method_annotations("Runner", &method);
    assert!(diags.is_empty());
}

#[test]
fn validate_module_fn_annotations_checks_trait_and_impl_methods() {
    let trait_def = TraitDef {
        public: false,
        name: sp("Additive".to_string()),
        doc: None,
        type_params: vec![],
        supertraits: vec![],
        fundeps: vec![],
        associated_types: vec![],
        methods: vec![TraitMethod {
            name: sp("add".to_string()),
            params: vec![
                Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("self".to_string())),
                    annotation: None,
                    default: None,
                },
                Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("other".to_string())),
                    annotation: None,
                    default: None,
                },
            ],
            return_annotation: None,
            effect_annotation: None,
            where_clause: vec![],
            default_body: None,
            doc: None,
            span: s(),
        }],
    };
    let impl_block = ImplBlock {
        trait_name: sp("Additive".to_string()),
        type_name: sp("Int".to_string()),
        type_params: vec![],
        methods: vec![FnDecl {
            annotations: vec![],
            public: false,
            name: sp("add".to_string()),
            doc: None,
            params: vec![
                Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("self".to_string())),
                    annotation: None,
                    default: None,
                },
                Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("other".to_string())),
                    annotation: None,
                    default: None,
                },
            ],
            return_annotation: Some(sp(TypeAnnotation::Named("Int".to_string()))),
            effect_annotation: None,
            body: lit_int(0),
            span: s(),
            where_clause: vec![],
            testing: None,
            testing_tags: Vec::new(),
        }],
        control_type: None,
        where_clause: vec![],
    };
    let module = Module {
        declarations: vec![
            sp(DeclKind::TraitDef(trait_def)),
            sp(DeclKind::ImplBlock(impl_block)),
        ],
        span: s(),
    };

    let diags = validate_module_fn_annotations(&module);
    assert_eq!(diags.len(), 3);
    assert_eq!(diags[0].message, "missing type annotation on parameter");
    assert_eq!(diags[1].message, "trait method missing return type");
    assert_eq!(diags[2].message, "missing type annotation on parameter");
}

#[test]
fn validate_module_fn_annotations_warns_on_legacy_effect_syntax() {
    let mut impure_fn = make_fn_decl("legacy_impure", vec![], lit_int(1));
    impure_fn.return_annotation = Some(sp(TypeAnnotation::Named("Int".to_string())));
    impure_fn.effect_annotation = Some(sp(EffectAnnotation::Impure));
    let mut volatile_fn = make_fn_decl("legacy_volatile", vec![], lit_int(1));
    volatile_fn.return_annotation = Some(sp(TypeAnnotation::Named("Int".to_string())));
    volatile_fn.effect_annotation = Some(sp(EffectAnnotation::Volatile));
    let module = Module {
        declarations: vec![
            sp(DeclKind::Function(impure_fn)),
            sp(DeclKind::Function(volatile_fn)),
        ],
        span: s(),
    };

    let diags = validate_module_fn_annotations(&module);
    assert!(
        diags.iter().any(|d| {
            matches!(d.severity, kea_diag::Severity::Warning)
                && d.message
                    .contains("legacy `impure` effect syntax is deprecated")
        }),
        "expected legacy effect deprecation warning, got {diags:?}"
    );
    assert!(
        diags.iter().any(|d| {
            matches!(d.severity, kea_diag::Severity::Warning)
                && d.message
                    .contains("legacy `volatile` effect syntax is deprecated")
        }),
        "expected volatile deprecation warning, got {diags:?}"
    );
}

#[test]
fn validate_module_annotations_unknown_annotation_suggests_known_name() {
    let mut fn_decl = make_fn_decl("old_api", vec!["x"], var("x"));
    fn_decl.annotations = vec![ann("renam", vec![ann_arg(lit_str("x"))])];
    fn_decl.params[0].annotation = Some(sp(TypeAnnotation::Named("Int".to_string())));
    fn_decl.return_annotation = Some(sp(TypeAnnotation::Named("Int".to_string())));

    let module = Module {
        declarations: vec![sp(DeclKind::Function(fn_decl))],
        span: s(),
    };

    let diags = validate_module_annotations(&module);
    assert_eq!(diags.len(), 1);
    assert!(diags[0].message.contains("unknown annotation `@renam`"));
    assert!(diags[0].message.contains("Did you mean `@rename`?"));
}

#[test]
fn validate_module_annotations_intrinsic_function_annotation_is_allowed() {
    let mut fn_decl = make_fn_decl("strlen", vec!["s"], lit_int(0));
    fn_decl.annotations = vec![ann("intrinsic", vec![ann_arg(lit_str("strlen"))])];
    fn_decl.params[0].annotation = Some(sp(TypeAnnotation::Named("String".to_string())));
    fn_decl.return_annotation = Some(sp(TypeAnnotation::Named("Int".to_string())));

    let module = Module {
        declarations: vec![sp(DeclKind::Function(fn_decl))],
        span: s(),
    };

    let diags = validate_module_annotations(&module);
    assert!(
        diags.is_empty(),
        "expected @intrinsic annotation to validate, got {diags:?}"
    );
}

#[test]
fn validate_module_annotations_intrinsic_requires_string_literal_argument() {
    let mut fn_decl = make_fn_decl("strlen", vec!["s"], lit_int(0));
    fn_decl.annotations = vec![ann("intrinsic", vec![ann_arg(lit_int(42))])];
    fn_decl.params[0].annotation = Some(sp(TypeAnnotation::Named("String".to_string())));
    fn_decl.return_annotation = Some(sp(TypeAnnotation::Named("Int".to_string())));

    let module = Module {
        declarations: vec![sp(DeclKind::Function(fn_decl))],
        span: s(),
    };

    let diags = validate_module_annotations(&module);
    assert!(
        diags
            .iter()
            .any(|d| d.message.contains("`@intrinsic` argument must be a string literal")),
        "expected @intrinsic string-literal diagnostic, got {diags:?}"
    );
}

#[test]
fn validate_module_annotations_default_literal_type_mismatch_errors() {
    let mut record = make_record_def(
        "Config",
        vec![("timeout", TypeAnnotation::Named("Int".into()))],
    );
    record.derives = vec![sp("Serialize".to_string())];
    record.field_annotations = vec![vec![ann("default", vec![ann_arg(lit_str("slow"))])]];
    let module = Module {
        declarations: vec![sp(DeclKind::RecordDef(record))],
        span: s(),
    };

    let diags = validate_module_annotations(&module);
    assert!(
        diags.iter().any(|d| d
            .message
            .contains("`@default` literal does not match field type annotation")),
        "expected default/type mismatch diagnostic, got {diags:?}"
    );
}

#[test]
fn validate_module_annotations_default_impure_argument_rejected() {
    let mut record = make_record_def(
        "Config",
        vec![("timeout", TypeAnnotation::Named("Int".into()))],
    );
    record.derives = vec![sp("Serialize".to_string())];
    record.field_annotations = vec![vec![ann(
        "default",
        vec![ann_arg(call(var("read_env"), vec![lit_str("TIMEOUT")]))],
    )]];
    let module = Module {
        declarations: vec![sp(DeclKind::RecordDef(record))],
        span: s(),
    };

    let diags = validate_module_annotations(&module);
    assert!(
        diags.iter().any(|d| d
            .message
            .contains("annotation arguments must be pure expressions")),
        "expected purity diagnostic, got {diags:?}"
    );
}

#[test]
fn validate_module_annotations_skip_if_option_guard_requires_optional_field() {
    let mut record = make_record_def(
        "Config",
        vec![("name", TypeAnnotation::Named("String".into()))],
    );
    record.derives = vec![sp("Serialize".to_string())];
    record.field_annotations = vec![vec![ann(
        "skip_if",
        vec![ann_arg(field_access(var("Option"), "is_none"))],
    )]];
    let module = Module {
        declarations: vec![sp(DeclKind::RecordDef(record))],
        span: s(),
    };

    let diags = validate_module_annotations(&module);
    assert!(
        diags.iter().any(|d| d
            .message
            .contains("`@skip_if(Option.is_none)` requires an optional field type")),
        "expected optional-field diagnostic, got {diags:?}"
    );
}

#[test]
fn validate_module_annotations_serialization_without_derive_is_warning() {
    let mut record = make_record_def(
        "Config",
        vec![("api_key", TypeAnnotation::Named("String".into()))],
    );
    record.field_annotations = vec![vec![ann("rename", vec![ann_arg(lit_str("apiKey"))])]];
    let module = Module {
        declarations: vec![sp(DeclKind::RecordDef(record))],
        span: s(),
    };

    let diags = validate_module_annotations(&module);
    assert_eq!(diags.len(), 1);
    assert!(matches!(diags[0].severity, kea_diag::Severity::Warning));
    assert!(
        diags[0]
            .message
            .contains("annotation `@rename` has no effect without `deriving Serialize`")
    );
}

#[test]
fn labeled_arguments_bind_with_registered_function_signature() {
    let mut env = TypeEnv::new();
    env.bind(
        "add".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Int, Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })),
    );
    env.set_function_signature(
        "add".to_string(),
        FnSignature {
            params: vec![
                FnParamSignature {
                    name: Some("x".to_string()),
                    label: None,
                    default: None,
                },
                FnParamSignature {
                    name: Some("y".to_string()),
                    label: Some("y".to_string()),
                    default: None,
                },
            ],
        },
    );

    let expr = call_with_args(
        var("add"),
        vec![
            Argument {
                label: None,
                value: lit_int(1),
            },
            labeled_arg("y", lit_int(2)),
        ],
    );
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let sum_types = SumTypeRegistry::new();
    let ty = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sum_types);

    assert!(
        !ctx.has_errors(),
        "unexpected diagnostics: {:?}",
        ctx.errors()
    );
    assert_eq!(ctx.substitution().apply(&ty), Type::Int);
}

#[test]
fn labeled_arguments_rejected_for_first_class_function_values() {
    let mut env = TypeEnv::new();
    env.bind(
        "f".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Int],
            ret: Box::new(Type::Int),
            effects: EffectRow::pure(),
        })),
    );

    let expr = call_with_args(var("f"), vec![labeled_arg("x", lit_int(1))]);
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let sum_types = SumTypeRegistry::new();
    let _ = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sum_types);

    assert!(ctx.has_errors(), "expected labeled call diagnostic");
    assert!(
        ctx.errors().iter().any(|d| d
            .message
            .contains("labeled arguments require a direct named function call")),
        "expected labeled-call eligibility diagnostic, got {:?}",
        ctx.errors()
    );
}

#[test]
fn dynamic_param_call_accepts_negative_literal_argument() {
    let mut env = TypeEnv::new();
    env.bind(
        "accept".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Dynamic],
            ret: Box::new(Type::Dynamic),
            effects: EffectRow::pure(),
        })),
    );

    let expr = call_with_args(
        var("accept"),
        vec![Argument {
            label: None,
            value: unary(UnaryOp::Neg, lit_int(1)),
        }],
    );
    let mut ctx = InferenceContext::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let sum_types = SumTypeRegistry::new();
    let _ = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sum_types);

    assert!(
        !ctx.has_errors(),
        "unexpected diagnostics for dynamic-parameter call: {:?}",
        ctx.errors()
    );
}

#[test]
fn handle_mismatched_effect_preserves_body_effects_without_phantom_io() {
    // Regression: handling an effect NOT present in the body's effect row
    // caused phantom IO from an unsatisfiable row decomposition constraint.
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("String".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let trace = make_effect_decl(
        "Trace",
        vec![],
        vec![make_effect_operation(
            "emit",
            vec![annotated_param(
                "value",
                TypeAnnotation::Named("Int".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let log_diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(
        log_diags.is_empty(),
        "unexpected diagnostics: {log_diags:?}"
    );
    let trace_diags = register_effect_decl(&trace, &records, Some(&sums), &mut env);
    assert!(
        trace_diags.is_empty(),
        "unexpected diagnostics: {trace_diags:?}"
    );

    let handled = call(field_access(var("Log"), "log"), vec![lit_str("hello")]);
    let clause = handle_clause(
        "Trace",
        "emit",
        vec![sp(PatternKind::Var("value".to_string()))],
        resume(lit_unit()),
    );
    let wrapper = make_fn_decl("wrapper", vec![], handle_expr(handled, vec![clause], None));

    let row = infer_fn_decl_effect_row(&wrapper, &env);
    assert!(
        row.row.has(&Label::new("Log")),
        "expected body Log effect to pass through mismatched handler, got {row:?}"
    );
    assert!(
        !row.row.has(&Label::new("IO")),
        "expected no phantom IO from mismatched handler, got {row:?}"
    );
}

#[test]
fn handle_mismatched_effect_preserves_reverse_direction_without_phantom_io() {
    // Reverse direction: body performs Trace, handler handles Log (absent).
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let sums = SumTypeRegistry::new();
    let mut traits = TraitRegistry::new();
    register_hkt_for_use_for_traits(&mut traits, &records);

    let log = make_effect_decl(
        "Log",
        vec![],
        vec![make_effect_operation(
            "log",
            vec![annotated_param(
                "msg",
                TypeAnnotation::Named("String".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let trace = make_effect_decl(
        "Trace",
        vec![],
        vec![make_effect_operation(
            "emit",
            vec![annotated_param(
                "value",
                TypeAnnotation::Named("Int".to_string()),
            )],
            TypeAnnotation::Named("Unit".to_string()),
        )],
    );
    let log_diags = register_effect_decl(&log, &records, Some(&sums), &mut env);
    assert!(
        log_diags.is_empty(),
        "unexpected diagnostics: {log_diags:?}"
    );
    let trace_diags = register_effect_decl(&trace, &records, Some(&sums), &mut env);
    assert!(
        trace_diags.is_empty(),
        "unexpected diagnostics: {trace_diags:?}"
    );

    let handled = call(field_access(var("Trace"), "emit"), vec![lit_int(1)]);
    let clause = handle_clause(
        "Log",
        "log",
        vec![sp(PatternKind::Var("msg".to_string()))],
        resume(lit_unit()),
    );
    let wrapper = make_fn_decl("wrapper", vec![], handle_expr(handled, vec![clause], None));

    let row = infer_fn_decl_effect_row(&wrapper, &env);
    assert!(
        row.row.has(&Label::new("Trace")),
        "expected body Trace effect to pass through mismatched handler, got {row:?}"
    );
    assert!(
        !row.row.has(&Label::new("IO")),
        "expected no phantom IO from mismatched handler, got {row:?}"
    );
}
