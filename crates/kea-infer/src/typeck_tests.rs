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

fn html_template(parts: Vec<StringInterpPart>, atoms: Vec<&str>) -> Expr {
    sp(ExprKind::EmbeddedBlock {
        kind: BlockKind::Html,
        parts,
        atom_fields: atoms.into_iter().map(|a| sp(a.to_string())).collect(),
        config: None,
    })
}

fn pipe(left: Expr, right: Expr) -> Expr {
    sp(ExprKind::Pipe {
        left: Box::new(left),
        op: sp(PipeOp::Standard),
        right: Box::new(right),
        guard: None,
    })
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

fn io_error_type() -> Type {
    builtin_error_sum_type("IOError").expect("IOError builtin type")
}

fn bind_io_reader(env: &mut TypeEnv, name: &str) {
    let tv = TypeVarId(9100);
    env.bind(
        name.to_string(),
        TypeScheme {
            type_vars: vec![tv],
            row_vars: vec![],
            dim_vars: vec![],
            lacks: BTreeMap::new(),
            bounds: BTreeMap::new(),
            kinds: BTreeMap::new(),
            ty: Type::Function(FunctionType {
                params: vec![Type::String],
                ret: Box::new(Type::Result(
                    Box::new(Type::DataFrame(Box::new(Type::Var(tv)))),
                    Box::new(io_error_type()),
                )),
            }),
        },
    );
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
fn check_expr_context_pushes_expected_precision_into_pipe_arguments() {
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let expr = pipe(lit_int(200), var("narrow"));
    let mut env = TypeEnv::new();
    env.bind(
        "narrow".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![expected.clone()],
            ret: Box::new(expected.clone()),
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
        "expected precision-range diagnostic from checked pipe arg, got {:?}",
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

#[test]
fn infer_html_template_is_row_polymorphic_function() {
    let expr = html_template(
        vec![
            StringInterpPart::Literal("<h1>".into()),
            StringInterpPart::Expr(Box::new(field_access(var("__row"), "name"))),
            StringInterpPart::Literal("</h1>".into()),
        ],
        vec!["name"],
    );
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "unexpected errors: {:?}", u.errors());
    match ty {
        Type::Function(ft) => {
            assert_eq!(*ft.ret, Type::Html);
            assert_eq!(ft.params.len(), 1);
            match &ft.params[0] {
                Type::AnonRecord(row) => {
                    assert!(row.get(&Label::new("name")).is_some());
                    assert!(row.is_open(), "template arg row should be open");
                }
                other => panic!("expected anon record param, got {other:?}"),
            }
        }
        other => panic!("expected function type, got {other:?}"),
    }
}

#[test]
fn infer_template_expr_interpolation_uses_lexical_scope() {
    let mut env = TypeEnv::new();
    env.bind("title".into(), TypeScheme::mono(Type::String));
    let expr = html_template(vec![StringInterpPart::Expr(Box::new(var("title")))], vec![]);
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(!u.has_errors(), "unexpected errors: {:?}", u.errors());
    match ty {
        Type::Function(ft) => assert_eq!(*ft.ret, Type::Html),
        other => panic!("expected function type, got {other:?}"),
    }
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
                    }),
                ],
                ret: Box::new(Type::Stream(Box::new(Type::Var(c)))),
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
                    }),
                ],
                ret: Box::new(Type::List(Box::new(Type::Var(c)))),
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
fn infer_if_pipe_guard_narrows_true_branch() {
    let mut env = TypeEnv::new();
    env.bind(
        "x".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Int))),
    );
    let expr = if_expr(
        pipe(var("x"), field_access(var("Option"), "is_some")),
        binop(BinOp::Add, var("x"), lit_int(1)),
        Some(lit_int(0)),
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "pipe guard should narrow true branch: {:?}",
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
fn infer_if_pipe_sum_variant_guard_narrows_branch() {
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
        pipe(var("s"), field_access(var("Shape"), "is_circle")),
        binop(BinOp::Eq, var("s"), lit_int(1)),
        Some(binop(BinOp::Eq, var("s"), lit_str("rect"))),
    );

    let ty = infer_and_resolve(&expr, &mut env, &mut unifier, &records, &traits, &sums);

    assert!(
        !unifier.has_errors(),
        "pipe sum guard should narrow branches: {:?}",
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

#[test]
fn infer_read_csv_with_schema_literal_narrows_result_dataframe() {
    let mut env = TypeEnv::new();
    bind_io_reader(&mut env, "read_csv");

    let schema = anon_record(vec![
        ("region", lit_str("String")),
        ("revenue", lit_str("Float")),
    ]);
    let expr = call(var("read_csv"), vec![lit_str("sales.csv"), schema]);
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "typed read_csv call should type-check: {:?}",
        u.errors()
    );

    let expected_row = RowType::closed(vec![
        (Label::new("region".to_string()), Type::String),
        (Label::new("revenue".to_string()), Type::Float),
    ]);
    assert_eq!(
        ty,
        Type::Result(
            Box::new(Type::DataFrame(Box::new(Type::AnonRecord(expected_row)))),
            Box::new(io_error_type())
        )
    );
}

#[test]
fn infer_read_csv_with_labeled_schema_arg_narrows_result_dataframe() {
    let mut env = TypeEnv::new();
    bind_io_reader(&mut env, "read_csv");

    let schema = anon_record(vec![
        ("region", lit_str("String")),
        ("revenue", lit_str("Float")),
    ]);
    let expr = call_with_args(
        var("read_csv"),
        vec![
            Argument {
                label: None,
                value: lit_str("sales.csv"),
            },
            labeled_arg("schema", schema),
        ],
    );
    let (ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        !u.has_errors(),
        "typed read_csv(schema:) call should type-check: {:?}",
        u.errors()
    );

    let expected_row = RowType::closed(vec![
        (Label::new("region".to_string()), Type::String),
        (Label::new("revenue".to_string()), Type::Float),
    ]);
    assert_eq!(
        ty,
        Type::Result(
            Box::new(Type::DataFrame(Box::new(Type::AnonRecord(expected_row)))),
            Box::new(io_error_type())
        )
    );
}

#[test]
fn infer_read_csv_with_unknown_schema_type_reports_error() {
    let mut env = TypeEnv::new();
    bind_io_reader(&mut env, "read_csv");

    let schema = anon_record(vec![("id", lit_str("MysteryType"))]);
    let expr = call(var("read_csv"), vec![lit_str("sales.csv"), schema]);
    let (_ty, u) = infer_with_env(&expr, &mut env);
    assert!(u.has_errors(), "unknown schema type should fail");
    assert!(
        u.errors()
            .iter()
            .any(|d| d.message.contains("unknown schema type")),
        "expected unknown schema type diagnostic, got: {:?}",
        u.errors()
    );
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
        })
    );
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
        })),
        Effects::pure_deterministic(),
    );
    env.register_module_type_scheme(
        "Kea.Map",
        "map_get",
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![Type::Bool],
            ret: Box::new(Type::Bool),
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
// Pipe operator
// ===========================================================================

#[test]
fn infer_pipe() {
    // { let double = |x| x + x; 21 |> double }  →  Int
    let expr = block(vec![
        let_bind(
            "double",
            lambda(&["x"], binop(BinOp::Add, var("x"), var("x"))),
        ),
        pipe(lit_int(21), var("double")),
    ]);
    let (ty, u) = infer(&expr);
    assert!(!u.has_errors(), "Errors: {:?}", u.errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_pipe_call_prepends_left_arg() {
    // { let pick_first = |a, b| a; 1 |> pick_first(2) }  -> Int
    let expr = block(vec![
        let_bind("pick_first", lambda(&["a", "b"], var("a"))),
        pipe(lit_int(1), call(var("pick_first"), vec![lit_int(2)])),
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
fn infer_pipe_pushes_expected_precision_into_arguments() {
    let expected = Type::IntN(IntWidth::I8, Signedness::Signed);
    let expr = pipe(lit_int(200), var("narrow"));
    let mut env = TypeEnv::new();
    env.bind(
        "narrow".to_string(),
        TypeScheme::mono(Type::Function(FunctionType {
            params: vec![expected.clone()],
            ret: Box::new(expected),
        })),
    );

    let (_ty, u) = infer_with_env(&expr, &mut env);
    assert!(
        u.has_errors(),
        "expected out-of-range literal error in infer-mode pipe"
    );
    let msg = u
        .errors()
        .iter()
        .map(|d| d.message.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(
        msg.contains("does not fit in"),
        "expected precision-range diagnostic from infer-mode pipe arg, got: {msg}"
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
fn infer_pipe_rejects_monomorphic_callback_for_rank2_parameter() {
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
        pipe(var("mono"), var("use_poly")),
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
fn infer_pipe_accepts_polymorphic_callback_for_rank2_parameter() {
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
        pipe(var("id"), var("use_poly")),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(
        !u.has_errors(),
        "expected polymorphic callback to satisfy rank-2 pipe contract: {:?}",
        u.errors()
    );
}

#[test]
fn infer_pipe_call_rejects_monomorphic_callback_for_rank2_parameter() {
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
        pipe(var("mono"), call(var("use_poly_with"), vec![lit_int(7)])),
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
fn infer_pipe_call_accepts_polymorphic_callback_for_rank2_parameter() {
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
        pipe(var("id"), call(var("use_poly_with"), vec![lit_int(7)])),
    ]);

    let (_ty, u) = infer(&expr);
    assert!(
        !u.has_errors(),
        "expected polymorphic callback to satisfy rank-2 pipe-call contract: {:?}",
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
                    && diag.message.contains("type `Either` expects 2 type arguments")
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
    let ann = TypeAnnotation::Applied(
        "Decimal".to_string(),
        vec![TypeAnnotation::DimLiteral(18)],
    );
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
    let ann = TypeAnnotation::Applied(
        "List".to_string(),
        vec![TypeAnnotation::DimLiteral(1)],
    );
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
    assert!(
        u.has_errors(),
        "List(1) should produce a type error"
    );
    assert!(
        u.errors().iter().any(|d| {
            d.message.contains("integer literal")
                && d.message.contains("not valid as a type")
        }),
        "expected dim-literal diagnostic, got: {:?}",
        u.errors().iter().map(|d| d.message.clone()).collect::<Vec<_>>()
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
fn bare_dataframe_annotation_creates_open_row() {
    // { let identity = |df: DataFrame| df  identity }
    // The binding should have type DataFrame(...) -> DataFrame(...)
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("identity".to_string())),
            annotation: None,
            value: Box::new(sp(ExprKind::Lambda {
                params: vec![kea_ast::Param {
                    label: ParamLabel::Implicit,
                    pattern: sp(PatternKind::Var("df".to_string())),
                    annotation: Some(sp(TypeAnnotation::Named("DataFrame".into()))),
                    default: None,
                }],
                body: Box::new(var("df")),
                return_annotation: None,
            })),
        }),
        var("identity"),
    ]);
    let (ty, u) = infer(&expr);
    assert!(
        !u.has_errors(),
        "bare DataFrame annotation should work: {:?}",
        u.errors()
    );
    let resolved = u.substitution.apply(&ty);
    match &resolved {
        Type::Function(ft) => {
            assert!(
                matches!(ft.params[0], Type::DataFrame(_)),
                "param should be DataFrame, got: {:?}",
                ft.params[0]
            );
        }
        _ => panic!("expected Function type, got: {:?}", resolved),
    }
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
    KindAnnotation::Arrow(Box::new(lhs), Box::new(rhs))
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
                sp(EffectAnnotation::Volatile),
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
    env.set_function_effect_term("poly_fn".to_string(), EffectTerm::Var(EffectVarId(77)));
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

    env.set_function_effect_term("pure_cb".to_string(), EffectTerm::Known(EffectLevel::Pure));
    let pure_call = call(var("apply"), vec![var("pure_cb")]);
    assert_eq!(
        infer_expr_effects(&pure_call, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_term(
        "impure_cb".to_string(),
        EffectTerm::Known(EffectLevel::Impure),
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

    env.set_function_effect_term("pure_cb".to_string(), EffectTerm::Known(EffectLevel::Pure));
    let pure_call = call(field_access(var("List"), "apply"), vec![var("pure_cb")]);
    assert_eq!(
        infer_expr_effects(&pure_call, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_term(
        "impure_cb".to_string(),
        EffectTerm::Known(EffectLevel::Impure),
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
fn infer_expr_effects_pipe_call_propagates_callback_effect_signature() {
    let mut env = TypeEnv::new();
    let mut map = make_fn_decl("map", vec!["xs", "f"], call(var("f"), vec![lit_int(1)]));
    map.params[1].annotation = Some(sp(TypeAnnotation::FunctionWithEffect(
        vec![TypeAnnotation::Named("Int".to_string())],
        sp(EffectAnnotation::Var("e".to_string())),
        Box::new(TypeAnnotation::Named("Int".to_string())),
    )));
    map.effect_annotation = Some(sp(EffectAnnotation::Var("e".to_string())));
    register_fn_effect_signature(&map, &mut env);

    env.set_function_effect_term("pure_cb".to_string(), EffectTerm::Known(EffectLevel::Pure));
    let pure_pipe = pipe(
        list(vec![lit_int(1)]),
        call(var("map"), vec![var("pure_cb")]),
    );
    assert_eq!(
        infer_expr_effects(&pure_pipe, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_term(
        "impure_cb".to_string(),
        EffectTerm::Known(EffectLevel::Impure),
    );
    let impure_pipe = pipe(
        list(vec![lit_int(1)]),
        call(var("map"), vec![var("impure_cb")]),
    );
    assert_eq!(infer_expr_effects(&impure_pipe, &env), Effects::impure());
}

#[test]
fn infer_expr_effects_pipe_qualified_call_propagates_callback_effect_signature() {
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

    env.set_function_effect_term("pure_cb".to_string(), EffectTerm::Known(EffectLevel::Pure));
    let pure_pipe = pipe(
        list(vec![lit_int(1)]),
        call(field_access(var("List"), "map"), vec![var("pure_cb")]),
    );
    assert_eq!(
        infer_expr_effects(&pure_pipe, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_term(
        "impure_cb".to_string(),
        EffectTerm::Known(EffectLevel::Impure),
    );
    let impure_pipe = pipe(
        list(vec![lit_int(1)]),
        call(field_access(var("List"), "map"), vec![var("impure_cb")]),
    );
    assert_eq!(infer_expr_effects(&impure_pipe, &env), Effects::impure());
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

    env.set_function_effect_term("pure_cb".to_string(), EffectTerm::Known(EffectLevel::Pure));
    env.set_function_effect_term(
        "volatile_cb".to_string(),
        EffectTerm::Known(EffectLevel::Volatile),
    );
    env.set_function_effect_term(
        "impure_cb".to_string(),
        EffectTerm::Known(EffectLevel::Impure),
    );

    let pure_call = call(var("zip_apply"), vec![var("pure_cb"), var("pure_cb")]);
    assert_eq!(
        infer_expr_effects(&pure_call, &env),
        Effects::pure_deterministic()
    );

    let volatile_call = call(var("zip_apply"), vec![var("pure_cb"), var("volatile_cb")]);
    // Shared `-[e]>` means both callback args must agree on the same effect
    // variable. `pure` + `volatile` is unsatisfiable under equality and
    // conservatively falls back to impure.
    assert_eq!(infer_expr_effects(&volatile_call, &env), Effects::impure());

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

    env.set_function_effect_term("pure_cb".to_string(), EffectTerm::Known(EffectLevel::Pure));
    let pure_expr = block(vec![
        let_bind("g", var("apply")),
        call(var("g"), vec![var("pure_cb")]),
    ]);
    assert_eq!(
        infer_expr_effects(&pure_expr, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_term(
        "impure_cb".to_string(),
        EffectTerm::Known(EffectLevel::Impure),
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

    env.set_function_effect_term("pure_cb".to_string(), EffectTerm::Known(EffectLevel::Pure));
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

    env.set_function_effect_term("pure_cb".to_string(), EffectTerm::Known(EffectLevel::Pure));
    let pure_expr = block(vec![
        let_bind("apply", apply_lambda.clone()),
        call(var("apply"), vec![var("pure_cb")]),
    ]);
    assert_eq!(
        infer_expr_effects(&pure_expr, &env),
        Effects::pure_deterministic()
    );

    env.set_function_effect_term(
        "impure_cb".to_string(),
        EffectTerm::Known(EffectLevel::Impure),
    );
    let impure_expr = block(vec![
        let_bind("apply", apply_lambda),
        call(var("apply"), vec![var("impure_cb")]),
    ]);
    assert_eq!(infer_expr_effects(&impure_expr, &env), Effects::impure());
}

#[test]
fn validate_declared_fn_effect_accepts_weaker_or_equal_inferred_effect() {
    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(EffectAnnotation::Impure));
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
fn validate_declared_fn_effect_rejects_open_row_with_concrete_entries() {
    let mut fn_decl = make_fn_decl("f", vec![], lit_int(1));
    fn_decl.effect_annotation = Some(sp(effect_row_annotation(
        vec![("IO", None)],
        Some("e"),
    )));
    let inferred = Effects::impure();
    let err = validate_declared_fn_effect(&fn_decl, inferred)
        .expect_err("open concrete rows should be rejected in compatibility contract checks");
    assert!(
        err.message
            .contains("open effect rows with concrete entries are not supported in contracts yet"),
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
            .contains("declared effect `-[e]>` does not match body effect behavior"),
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
        err.message.contains("trait `Runner` requires `pure`"),
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
        err.message
            .contains("declared effect `-[impl_e]>` does not match body effect behavior"),
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
fn trait_impl_kind_mismatch_reports_clear_error() {
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

    let err = traits
        .register_trait_impl(&make_impl_block("Bind", "Int", vec![]))
        .unwrap_err();
    assert!(err.message.contains("kind mismatch in Bind implementation"));
    assert!(
        err.help
            .as_ref()
            .is_some_and(|h| h.contains("Int has kind *"))
    );
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
fn trait_impl_kind_uses_named_self_param_when_present() {
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

    // Should validate against the `Self` kind (* -> *), not the first parameter (`X`: *).
    traits
        .register_trait_impl(&make_impl_block("NamedSelf", "List", vec![]))
        .expect("List should satisfy named Self kind");

    let err = traits
        .register_trait_impl(&make_impl_block("NamedSelf", "Int", vec![]))
        .expect_err("Int should violate named Self kind");
    assert!(
        err.message
            .contains("kind mismatch in NamedSelf implementation")
    );
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
fn trait_impl_kind_mismatch_uses_first_trait_type_param_kind() {
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

    let err = traits
        .register_trait_impl(&make_impl_block("BiLike", "Int", vec![]))
        .unwrap_err();
    assert!(
        err.message
            .contains("kind mismatch in BiLike implementation")
    );
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
fn ownership_scope_rill_builtin() {
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

// ===========================================================================
// DataFrame type-level operations (KERNEL §7)
// ===========================================================================

fn df_row(fields: Vec<(&str, Type)>) -> Type {
    let row = RowType::closed(
        fields
            .into_iter()
            .map(|(n, t)| (Label::new(n.to_string()), t))
            .collect(),
    );
    Type::DataFrame(Box::new(Type::AnonRecord(row)))
}

#[test]
fn dataframe_unification_same_schema() {
    let mut u = Unifier::new();
    let df1 = df_row(vec![("a", Type::Int), ("b", Type::String)]);
    let df2 = df_row(vec![("a", Type::Int), ("b", Type::String)]);
    let prov = Provenance {
        span: s(),
        reason: Reason::LetAnnotation,
    };
    u.unify(&df1, &df2, &prov);
    assert!(
        !u.has_errors(),
        "same-schema DataFrames should unify: {:?}",
        u.errors()
    );
}

#[test]
fn dataframe_unification_different_schema_errors() {
    let mut u = Unifier::new();
    let df1 = df_row(vec![("a", Type::Int)]);
    let df2 = df_row(vec![("a", Type::String)]);
    let prov = Provenance {
        span: s(),
        reason: Reason::LetAnnotation,
    };
    u.unify(&df1, &df2, &prov);
    assert!(u.has_errors(), "different-type fields should not unify");
}

#[test]
fn dataframe_dynamic_does_not_unify_with_typed() {
    let mut u = Unifier::new();
    let dynamic = Type::DataFrame(Box::new(Type::Dynamic));
    let typed = df_row(vec![("a", Type::Int)]);
    let prov = Provenance {
        span: s(),
        reason: Reason::DataFrameExpectSchema,
    };
    u.unify(&dynamic, &typed, &prov);
    assert!(
        u.has_errors(),
        "DataFrame(Dynamic) should not unify with DataFrame({{a: Int}})"
    );
}

#[test]
fn dataframe_dynamic_unifies_with_self() {
    let mut u = Unifier::new();
    let d1 = Type::DataFrame(Box::new(Type::Dynamic));
    let d2 = Type::DataFrame(Box::new(Type::Dynamic));
    let prov = Provenance {
        span: s(),
        reason: Reason::LetAnnotation,
    };
    u.unify(&d1, &d2, &prov);
    assert!(
        !u.has_errors(),
        "DataFrame(Dynamic) should unify with itself"
    );
}

#[test]
fn dataframe_expect_schema_narrows() {
    let mut u = Unifier::new();
    let input = Type::DataFrame(Box::new(Type::Dynamic));
    let expected_row = RowType::closed(vec![
        (Label::new("x"), Type::Int),
        (Label::new("y"), Type::Float),
    ]);
    let result_ty = df_expect_schema(&input, expected_row, &mut u, s());
    assert!(
        !u.has_errors(),
        "expect_schema on Dynamic should succeed: {:?}",
        u.errors()
    );
    // Result should be Result(DataFrame({x: Int, y: Float}), String)
    match u.substitution.apply(&result_ty) {
        Type::Result(ok, _err) => match *ok {
            Type::DataFrame(inner) => match *inner {
                Type::AnonRecord(row) => {
                    assert_eq!(row.fields.len(), 2);
                    assert_eq!(row.fields[0].0, Label::new("x"));
                }
                other => panic!("expected AnonRecord, got {other:?}"),
            },
            other => panic!("expected DataFrame, got {other:?}"),
        },
        other => panic!("expected Result, got {other:?}"),
    }
}

#[test]
fn dataframe_expect_schema_rejects_non_dynamic() {
    let mut u = Unifier::new();
    let input = df_row(vec![("a", Type::Int)]);
    let expected_row = RowType::closed(vec![(Label::new("x"), Type::Int)]);
    let _result_ty = df_expect_schema(&input, expected_row, &mut u, s());
    assert!(
        u.has_errors(),
        "expect_schema on typed DataFrame should error"
    );
}

#[test]
fn dataframe_mutate_adds_column() {
    let mut u = Unifier::new();
    let input = df_row(vec![("a", Type::Int)]);
    let result_ty = df_mutate(&input, Label::new("b"), Type::String, &mut u, s());
    assert!(!u.has_errors(), "mutate should succeed: {:?}", u.errors());
    let resolved = u.substitution.apply(&result_ty);
    // Should be DataFrame({b: String | row}) where row resolved to {a: Int}
    match resolved {
        Type::DataFrame(inner) => match *inner {
            Type::AnonRecord(row) => {
                let labels: Vec<_> = row.fields.iter().map(|(l, _)| l.as_str()).collect();
                assert!(labels.contains(&"a"), "should contain 'a': {labels:?}");
                assert!(labels.contains(&"b"), "should contain 'b': {labels:?}");
            }
            other => panic!("expected AnonRecord, got {other:?}"),
        },
        other => panic!("expected DataFrame, got {other:?}"),
    }
}

#[test]
fn dataframe_mutate_duplicate_column_errors() {
    let mut u = Unifier::new();
    let input = df_row(vec![("a", Type::Int)]);
    let _result_ty = df_mutate(&input, Label::new("a"), Type::String, &mut u, s());
    assert!(
        u.has_errors(),
        "mutate with existing column name should error (lacks violation)"
    );
}

#[test]
fn dataframe_update_same_type_succeeds() {
    let mut u = Unifier::new();
    let input = df_row(vec![("a", Type::Int), ("b", Type::String)]);
    let result_ty = df_update(&input, Label::new("a"), &Type::Int, &mut u, s());
    assert!(
        !u.has_errors(),
        "update same type should succeed: {:?}",
        u.errors()
    );
    let resolved = u.substitution.apply(&result_ty);
    match resolved {
        Type::DataFrame(_) => {} // Just verify it's a DataFrame
        other => panic!("expected DataFrame, got {other:?}"),
    }
}

#[test]
fn dataframe_update_different_type_errors() {
    let mut u = Unifier::new();
    let input = df_row(vec![("a", Type::Int), ("b", Type::String)]);
    let _result_ty = df_update(
        &input,
        Label::new("a"),
        &Type::String, // Wrong type — `a` is Int
        &mut u,
        s(),
    );
    assert!(u.has_errors(), "update with wrong type should error");
}

#[test]
fn dataframe_drop_removes_column() {
    let mut u = Unifier::new();
    let input = df_row(vec![("a", Type::Int), ("b", Type::String)]);
    let result_ty = df_drop(&input, Label::new("a"), &mut u, s());
    assert!(!u.has_errors(), "drop should succeed: {:?}", u.errors());
    let resolved = u.substitution.apply(&result_ty);
    match resolved {
        Type::DataFrame(inner) => match *inner {
            Type::AnonRecord(row) => {
                let labels: Vec<_> = row.fields.iter().map(|(l, _)| l.as_str()).collect();
                assert!(!labels.contains(&"a"), "should NOT contain 'a': {labels:?}");
                assert!(labels.contains(&"b"), "should contain 'b': {labels:?}");
            }
            other => panic!("expected AnonRecord, got {other:?}"),
        },
        other => panic!("expected DataFrame, got {other:?}"),
    }
}

#[test]
fn dataframe_drop_missing_column_errors() {
    let mut u = Unifier::new();
    let input = df_row(vec![("a", Type::Int)]);
    let _result_ty = df_drop(&input, Label::new("nonexistent"), &mut u, s());
    assert!(u.has_errors(), "drop missing column should error");
}

#[test]
fn dataframe_join_matching_keys() {
    let mut u = Unifier::new();
    let left = RowType::closed(vec![
        (Label::new("id"), Type::Int),
        (Label::new("name"), Type::String),
    ]);
    let right = RowType::closed(vec![
        (Label::new("id"), Type::Int),
        (Label::new("age"), Type::Int),
    ]);
    let result = df_join_check(&left, &right, &[Label::new("id")], &mut u, s());
    assert!(
        !u.has_errors(),
        "join with matching key types should not produce unifier errors"
    );
    assert!(result.is_ok(), "join with matching keys should succeed");
    let joined_ty = result.unwrap();
    match joined_ty {
        Type::DataFrame(inner) => match *inner {
            Type::AnonRecord(row) => {
                let labels: Vec<_> = row.fields.iter().map(|(l, _)| l.as_str()).collect();
                assert!(
                    labels.contains(&"id"),
                    "should contain key 'id': {labels:?}"
                );
                assert!(
                    labels.contains(&"name"),
                    "should contain 'name': {labels:?}"
                );
                assert!(labels.contains(&"age"), "should contain 'age': {labels:?}");
            }
            other => panic!("expected AnonRecord, got {other:?}"),
        },
        other => panic!("expected DataFrame, got {other:?}"),
    }
}

#[test]
fn dataframe_join_mismatched_key_types() {
    let mut u = Unifier::new();
    let left = RowType::closed(vec![
        (Label::new("id"), Type::Int),
        (Label::new("name"), Type::String),
    ]);
    let right = RowType::closed(vec![
        (Label::new("id"), Type::String), // Key type mismatch!
        (Label::new("age"), Type::Int),
    ]);
    let _result = df_join_check(&left, &right, &[Label::new("id")], &mut u, s());
    assert!(
        u.has_errors(),
        "join with mismatched key types should error"
    );
}

#[test]
fn dataframe_join_overlapping_non_key_columns() {
    let mut u = Unifier::new();
    let left = RowType::closed(vec![
        (Label::new("id"), Type::Int),
        (Label::new("value"), Type::String),
    ]);
    let right = RowType::closed(vec![
        (Label::new("id"), Type::Int),
        (Label::new("value"), Type::Int), // Overlapping non-key column!
    ]);
    let result = df_join_check(&left, &right, &[Label::new("id")], &mut u, s());
    assert!(
        result.is_err(),
        "join with overlapping non-key columns should error"
    );
    let msg = result.unwrap_err().message;
    assert!(msg.contains("duplicate column `value`"), "got: {msg}");
}

#[test]
fn dataframe_join_missing_key_in_left() {
    let u = &mut Unifier::new();
    let left = RowType::closed(vec![(Label::new("name"), Type::String)]);
    let right = RowType::closed(vec![
        (Label::new("id"), Type::Int),
        (Label::new("age"), Type::Int),
    ]);
    let result = df_join_check(&left, &right, &[Label::new("id")], u, s());
    assert!(result.is_err());
    let msg = result.unwrap_err().message;
    assert!(msg.contains("not found in left"), "got: {msg}");
}

#[test]
fn dataframe_row_polymorphic_function() {
    // A function that works on any DataFrame with an `a: Int` column
    // fn sum_a(df: DataFrame({a: Int | r})) -> Int
    let mut env = TypeEnv::new();
    let mut u = Unifier::new();
    let records = RecordRegistry::new();

    // Build: let sum_a = |df| df  (identity, just testing the type)
    let expr = block(vec![
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("identity".to_string())),
            annotation: None,
            value: Box::new(lambda(&["x"], var("x"))),
        }),
        // Apply identity to a DataFrame literal (we can't construct one,
        // so just verify the type of a let-bound variable)
        sp(ExprKind::Let {
            pattern: sp(PatternKind::Var("df".to_string())),
            annotation: None,
            value: Box::new(sp(ExprKind::Var("identity".to_string()))),
        }),
        var("df"),
    ]);
    let traits = TraitRegistry::new();
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut u,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!u.has_errors(), "should not error: {:?}", u.errors());
    // Type should be polymorphic (a -> a)
    let resolved = u.substitution.apply(&ty);
    // Type is polymorphic identity (a -> a) or unresolved var — both valid
    let _ = resolved;
}

// ===========================================================================
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
fn error_msg_lacks_violation() {
    // Test duplicate column in DataFrame context
    let mut u = Unifier::new();
    let input = df_row(vec![("total", Type::Int)]);
    let _ = df_mutate(&input, Label::new("total"), Type::Float, &mut u, s());
    assert!(u.has_errors());
    let msg = &u.errors()[0].message;
    assert!(msg.contains("cannot add column `total`"), "got: {msg}");
    assert!(
        msg.contains("already has a column named `total`"),
        "got: {msg}"
    );
    // Should suggest using update
    assert!(
        u.errors()[0]
            .help
            .as_ref()
            .is_some_and(|h| h.contains("update"))
    );
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
fn error_msg_dataframe_context_uses_column() {
    // Missing field in DataFrame context should say "column" not "field"
    let errors = row_errors_with_reason(
        vec![("id", Type::Int), ("name", Type::String)],
        vec![("id", Type::Int)],
        Reason::DataFrameExpectSchema,
    );
    assert_eq!(errors.len(), 1);
    assert!(
        errors[0].message.contains("missing column `name`"),
        "got: {}",
        errors[0].message
    );
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
        missing_age_count, 1,
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
    assert_eq!(
        unifier.type_var_kinds.get(&f_tv),
        Some(&Kind::Arrow(Box::new(Kind::Star), Box::new(Kind::Star)))
    );
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
    assert_eq!(
        unifier.type_var_kinds.get(&f_tv),
        Some(&Kind::Arrow(Box::new(Kind::Star), Box::new(Kind::Star)))
    );
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
    assert_eq!(
        scheme.kinds.get(&f_tv),
        Some(&Kind::Arrow(Box::new(Kind::Star), Box::new(Kind::Star)))
    );
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

    let expected_hkt_kind = Kind::Arrow(Box::new(Kind::Star), Box::new(Kind::Star));
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
// Frame literal type inference
// =========================================================================

fn frame_literal(columns: Vec<(&str, Vec<Expr>)>) -> Expr {
    sp(ExprKind::Frame {
        columns: columns
            .into_iter()
            .map(|(name, values)| (sp(name.to_string()), values))
            .collect(),
    })
}

fn sql_expr(body: &str) -> Expr {
    sp(ExprKind::EmbeddedBlock {
        kind: BlockKind::Sql,
        parts: vec![StringInterpPart::Literal(body.to_string())],
        atom_fields: vec![],
        config: None,
    })
}

fn sql_expr_with_config(body: &str, config: Vec<(&str, Expr)>) -> Expr {
    sp(ExprKind::EmbeddedBlock {
        kind: BlockKind::Sql,
        parts: vec![StringInterpPart::Literal(body.to_string())],
        atom_fields: vec![],
        config: Some(
            config
                .into_iter()
                .map(|(k, v)| (sp(k.to_string()), v))
                .collect(),
        ),
    })
}

#[test]
fn infer_frame_literal_int_column() {
    let expr = frame_literal(vec![("x", vec![lit_int(1), lit_int(2), lit_int(3)])]);
    let mut env = TypeEnv::new();
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
    assert!(!unifier.has_errors(), "{:?}", unifier.errors());
    // Should be DataFrame(#{ x: Int })
    match &ty {
        Type::DataFrame(inner) => match inner.as_ref() {
            Type::AnonRecord(row) => {
                assert_eq!(row.fields.len(), 1);
                assert_eq!(row.get(&Label::new("x")), Some(&Type::Int));
            }
            other => panic!("expected AnonRecord, got {other:?}"),
        },
        other => panic!("expected DataFrame, got {other:?}"),
    }
}

#[test]
fn infer_sql_with_source_requires_connection() {
    let expr = sql_expr_with_config("SELECT 1 AS x", vec![("source", lit_int(1))]);
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
    assert!(unifier.has_errors(), "source must be Connection");
}

#[test]
fn infer_sql_with_source_returns_dynamic_dataframe() {
    let expr = sql_expr_with_config("SELECT 1 AS x", vec![("source", var("conn"))]);
    let mut env = TypeEnv::new();
    env.bind(
        "conn".into(),
        TypeScheme::mono(Type::Opaque {
            name: "Connection".to_string(),
            params: vec![],
        }),
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
    assert!(!unifier.has_errors(), "{:?}", unifier.errors());
    assert_eq!(ty, Type::DataFrame(Box::new(Type::Dynamic)));
}

#[test]
fn infer_frame_literal_multi_column() {
    let expr = frame_literal(vec![
        ("name", vec![lit_str("Alice"), lit_str("Bob")]),
        ("age", vec![lit_int(30), lit_int(25)]),
    ]);
    let mut env = TypeEnv::new();
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
    assert!(!unifier.has_errors(), "{:?}", unifier.errors());
    match &ty {
        Type::DataFrame(inner) => match inner.as_ref() {
            Type::AnonRecord(row) => {
                assert_eq!(row.fields.len(), 2);
                assert_eq!(row.get(&Label::new("age")), Some(&Type::Int));
                assert_eq!(row.get(&Label::new("name")), Some(&Type::String));
            }
            other => panic!("expected AnonRecord, got {other:?}"),
        },
        other => panic!("expected DataFrame, got {other:?}"),
    }
}

#[test]
fn infer_frame_literal_mixed_types_error() {
    let expr = frame_literal(vec![("x", vec![lit_int(1), lit_str("oops")])]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors(), "mixed types should produce an error");
}

#[test]
fn infer_frame_literal_empty_error() {
    let expr = frame_literal(vec![]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors(), "empty frame should produce an error");
}

#[test]
fn infer_frame_literal_mismatched_lengths_error() {
    let expr = frame_literal(vec![
        ("x", vec![lit_int(1), lit_int(2)]),
        ("y", vec![lit_int(1)]),
    ]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "mismatched column lengths should produce an error"
    );
}

#[test]
fn infer_frame_literal_nullable_column() {
    // frame { x: [1, None, 3] } → DataFrame(#{ x: Int? })
    let expr = frame_literal(vec![("x", vec![lit_int(1), none_expr(), lit_int(3)])]);
    let mut env = TypeEnv::new();
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
        "nullable column should not error: {:?}",
        unifier.errors()
    );
    // Type should be DataFrame(#{ x: Int? })
    match &ty {
        Type::DataFrame(inner) => match inner.as_ref() {
            Type::AnonRecord(row) => {
                assert_eq!(row.fields.len(), 1);
                assert_eq!(row.fields[0].0, Label::new("x"));
                match &row.fields[0].1 {
                    Type::Option(inner) => assert_eq!(**inner, Type::Int),
                    other => panic!("expected Option(Int), got {other}"),
                }
            }
            other => panic!("expected AnonRecord, got {other}"),
        },
        other => panic!("expected DataFrame, got {other}"),
    }
}

#[test]
fn infer_frame_literal_nullable_multi_column() {
    // frame { name: ["Alice", None], age: [30, 25] }
    // → DataFrame(#{ age: Int, name: String? })
    let expr = frame_literal(vec![
        ("name", vec![lit_str("Alice"), none_expr()]),
        ("age", vec![lit_int(30), lit_int(25)]),
    ]);
    let mut env = TypeEnv::new();
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
        "mixed nullable/non-nullable columns should not error: {:?}",
        unifier.errors()
    );
    match &ty {
        Type::DataFrame(inner) => match inner.as_ref() {
            Type::AnonRecord(row) => {
                assert_eq!(row.fields.len(), 2);
                // Fields are sorted: age, name
                assert_eq!(row.fields[0].0, Label::new("age"));
                assert_eq!(row.fields[0].1, Type::Int);
                assert_eq!(row.fields[1].0, Label::new("name"));
                match &row.fields[1].1 {
                    Type::Option(inner) => assert_eq!(**inner, Type::String),
                    other => panic!("expected Option(String), got {other}"),
                }
            }
            other => panic!("expected AnonRecord, got {other}"),
        },
        other => panic!("expected DataFrame, got {other}"),
    }
}

#[test]
fn infer_frame_literal_all_none_error() {
    // frame { x: [None, None] } → error
    let expr = frame_literal(vec![("x", vec![none_expr(), none_expr()])]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "all-None column should produce an error"
    );
    assert!(
        unifier.errors()[0].message.contains("only None"),
        "error should mention 'only None', got: {}",
        unifier.errors()[0].message
    );
}

#[test]
fn infer_frame_literal_duplicate_column_error() {
    let expr = frame_literal(vec![
        ("x", vec![lit_int(1), lit_int(2)]),
        ("x", vec![lit_int(3), lit_int(4)]),
    ]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "duplicate column names should produce an error"
    );
    assert!(
        unifier.errors()[0].message.contains("duplicate column"),
        "error should mention duplicate column, got: {}",
        unifier.errors()[0].message
    );
}

#[test]
fn infer_sql_select_star_from_typed_dataframe() {
    let mut env = TypeEnv::new();
    let row = RowType::closed(vec![(Label::new("x"), Type::Int)]);
    env.bind(
        "t".to_string(),
        TypeScheme::mono(Type::DataFrame(Box::new(Type::AnonRecord(row.clone())))),
    );

    let expr = sql_expr("SELECT * FROM t");
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
        "sql type inference failed: {:?}",
        unifier.errors()
    );
    assert_eq!(ty, Type::DataFrame(Box::new(Type::AnonRecord(row))));
}

#[test]
fn infer_sql_select_projection_infers_output_columns() {
    let mut env = TypeEnv::new();
    let input_row = RowType::closed(vec![
        (Label::new("x"), Type::Int),
        (Label::new("name"), Type::String),
    ]);
    env.bind(
        "t".to_string(),
        TypeScheme::mono(Type::DataFrame(Box::new(Type::AnonRecord(input_row)))),
    );

    let expr = sql_expr("SELECT name FROM t");
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
        "sql type inference failed: {:?}",
        unifier.errors()
    );
    let expected_row = RowType::closed(vec![(Label::new("name"), Type::String)]);
    assert_eq!(
        ty,
        Type::DataFrame(Box::new(Type::AnonRecord(expected_row)))
    );
}

#[test]
fn infer_sql_unknown_column_reports_error() {
    let mut env = TypeEnv::new();
    let input_row = RowType::closed(vec![(Label::new("x"), Type::Int)]);
    env.bind(
        "t".to_string(),
        TypeScheme::mono(Type::DataFrame(Box::new(Type::AnonRecord(input_row)))),
    );

    let expr = sql_expr("SELECT y FROM t");
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(unifier.has_errors(), "expected sql unknown-column error");
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("unknown column `y`")),
        "expected unknown column diagnostic, got {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_sql_cte_projection_infers_schema() {
    let mut env = TypeEnv::new();
    let input_row = RowType::closed(vec![
        (Label::new("x"), Type::Int),
        (Label::new("name"), Type::String),
    ]);
    env.bind(
        "t".to_string(),
        TypeScheme::mono(Type::DataFrame(Box::new(Type::AnonRecord(input_row)))),
    );

    let expr = sql_expr("WITH u AS (SELECT name FROM t) SELECT * FROM u");
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
        "sql CTE inference failed: {:?}",
        unifier.errors()
    );
    let expected_row = RowType::closed(vec![(Label::new("name"), Type::String)]);
    assert_eq!(
        ty,
        Type::DataFrame(Box::new(Type::AnonRecord(expected_row)))
    );
}

#[test]
fn infer_sql_derived_subquery_alias_infers_schema() {
    let mut env = TypeEnv::new();
    let input_row = RowType::closed(vec![
        (Label::new("x"), Type::Int),
        (Label::new("name"), Type::String),
    ]);
    env.bind(
        "t".to_string(),
        TypeScheme::mono(Type::DataFrame(Box::new(Type::AnonRecord(input_row)))),
    );

    let expr = sql_expr("SELECT s.name FROM (SELECT name FROM t) AS s");
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
        "sql subquery inference failed: {:?}",
        unifier.errors()
    );
    let expected_row = RowType::closed(vec![(Label::new("name"), Type::String)]);
    assert_eq!(
        ty,
        Type::DataFrame(Box::new(Type::AnonRecord(expected_row)))
    );
}

#[test]
fn infer_sql_union_projection_infers_schema() {
    let mut env = TypeEnv::new();
    let row = RowType::closed(vec![(Label::new("x"), Type::Int)]);
    env.bind(
        "t".to_string(),
        TypeScheme::mono(Type::DataFrame(Box::new(Type::AnonRecord(row)))),
    );

    let expr = sql_expr("SELECT x FROM t UNION SELECT x FROM t");
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
        "sql union inference failed: {:?}",
        unifier.errors()
    );
    let expected_row = RowType::closed(vec![(Label::new("x"), Type::Int)]);
    assert_eq!(
        ty,
        Type::DataFrame(Box::new(Type::AnonRecord(expected_row)))
    );
}

#[test]
fn infer_sql_union_mismatched_column_count_errors() {
    let mut env = TypeEnv::new();
    let row = RowType::closed(vec![
        (Label::new("x"), Type::Int),
        (Label::new("name"), Type::String),
    ]);
    env.bind(
        "t".to_string(),
        TypeScheme::mono(Type::DataFrame(Box::new(Type::AnonRecord(row)))),
    );

    let expr = sql_expr("SELECT x FROM t UNION SELECT x, name FROM t");
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "expected mismatched union columns error"
    );
    assert!(
        unifier.errors().iter().any(|d| d
            .message
            .contains("set operation has mismatched column counts")),
        "expected mismatched set-op diagnostic, got {:?}",
        unifier.errors()
    );
}

// ---------------------------------------------------------------------------
// DfVerb type inference helpers
// ---------------------------------------------------------------------------

fn col_atom(name: &str) -> ColExpr {
    sp(ColExprKind::Atom(name.to_string()))
}

fn col_lit_int(n: i64) -> ColExpr {
    sp(ColExprKind::Lit(Lit::Int(n)))
}

fn col_lit_str(s: &str) -> ColExpr {
    sp(ColExprKind::Lit(Lit::String(s.to_string())))
}

fn col_binop(op: BinOp, left: ColExpr, right: ColExpr) -> ColExpr {
    sp(ColExprKind::BinaryOp {
        op: sp(op),
        left: Box::new(left),
        right: Box::new(right),
    })
}

fn col_call(func: &str, args: Vec<ColExpr>) -> ColExpr {
    sp(ColExprKind::Call {
        func: sp(func.to_string()),
        args,
    })
}

fn col_range(start: ColExpr, end: ColExpr, inclusive: bool) -> ColExpr {
    sp(ColExprKind::Range {
        start: Box::new(start),
        end: Box::new(end),
        inclusive,
    })
}

fn df_verb(verb_kind: DfVerbKind, args: DfVerbArgs) -> Expr {
    sp(ExprKind::DfVerb {
        verb: sp(verb_kind),
        args,
    })
}

fn df_pipe(left: Expr, right: Expr) -> Expr {
    sp(ExprKind::Pipe {
        left: Box::new(left),
        op: sp(PipeOp::Standard),
        right: Box::new(right),
        guard: None,
    })
}

// ---------------------------------------------------------------------------
// DfVerb type inference tests
// ---------------------------------------------------------------------------

#[test]
fn infer_df_verb_filter_preserves_schema() {
    // frame { age: [30, 25], name: ["Alice", "Bob"] } |> filter(:age > 28)
    let df = frame_literal(vec![
        ("age", vec![lit_int(30), lit_int(25)]),
        ("name", vec![lit_str("Alice"), lit_str("Bob")]),
    ]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Gt, col_atom("age"), col_lit_int(28))),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
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
        "filter should not produce errors, got: {:?}",
        unifier.errors()
    );

    // Result should be DataFrame(#{age: Int, name: String})
    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            assert_eq!(row.fields.len(), 2);
            let age_field = row.fields.iter().find(|(l, _)| l.as_str() == "age");
            assert!(age_field.is_some(), "result should have 'age' column");
            assert_eq!(age_field.unwrap().1, Type::Int);
        } else {
            panic!("expected AnonRecord inside DataFrame, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_df_verb_filter_non_bool_error() {
    // filter(:age + 1) should error — result is Int, not Bool
    let df = frame_literal(vec![("age", vec![lit_int(30)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Add, col_atom("age"), col_lit_int(1))),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "filter with Int result should produce an error"
    );
}

#[test]
fn infer_df_verb_filter_in_range_typechecks() {
    let df = frame_literal(vec![("age", vec![lit_int(30), lit_int(25), lit_int(70)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(
            BinOp::In,
            col_atom("age"),
            col_range(col_lit_int(18), col_lit_int(65), true),
        )),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        !unifier.has_errors(),
        "filter with range membership should type-check: {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_df_verb_filter_in_range_mismatch_errors() {
    let df = frame_literal(vec![("age", vec![lit_int(30), lit_int(25), lit_int(70)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(
            BinOp::In,
            col_atom("age"),
            col_range(col_lit_float(18.0), col_lit_float(65.0), true),
        )),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "range element type mismatch should produce an error"
    );
}

#[test]
fn infer_df_verb_head_accepts_precision_integer_count() {
    let df = frame_literal(vec![("age", vec![lit_int(30), lit_int(25)])]);
    let head = df_verb(DfVerbKind::Head, DfVerbArgs::Head(Box::new(var("n8"))));
    let expr = df_pipe(df, head);

    let mut env = TypeEnv::new();
    env.bind(
        "n8".into(),
        TypeScheme::mono(Type::IntN(IntWidth::I8, Signedness::Signed)),
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
        "head with Int8 count should not error: {:?}",
        unifier.errors()
    );
    assert!(
        matches!(ty, Type::DataFrame(_)),
        "head should preserve DataFrame type, got {ty:?}"
    );
}

#[test]
fn infer_df_verb_head_rejects_non_integer_count() {
    let df = frame_literal(vec![("age", vec![lit_int(30), lit_int(25)])]);
    let head = df_verb(DfVerbKind::Head, DfVerbArgs::Head(Box::new(lit_str("2"))));
    let expr = df_pipe(df, head);

    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();

    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(unifier.has_errors(), "head with String count should error");
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("expects an integer count")),
        "expected integer-count diagnostic, got {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_mutate_decimal_addition_computes_result_dimensions() {
    let mut env = TypeEnv::new();
    let input_row = RowType::closed(vec![
        (Label::new("price"), decimal(10, 2)),
        (Label::new("fee"), decimal(12, 4)),
    ]);
    env.bind(
        "trades".into(),
        TypeScheme::mono(Type::DataFrame(Box::new(Type::AnonRecord(input_row)))),
    );

    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("total".into()),
            col_binop(BinOp::Add, col_atom("price"), col_atom("fee")),
        )]),
    );
    let expr = df_pipe(var("trades"), mutate);

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
        "decimal mutate should type-check, got: {:?}",
        unifier.errors()
    );
    let Type::DataFrame(inner) = ty else {
        panic!("expected DataFrame result");
    };
    let Type::AnonRecord(row) = *inner else {
        panic!("expected DataFrame anonymous row");
    };
    let total = row
        .fields
        .iter()
        .find(|(label, _)| label.as_str() == "total")
        .expect("mutate result should contain total");
    assert_eq!(total.1, decimal(13, 4));
}

#[test]
fn infer_df_verb_select_restricts_schema() {
    // frame { a: [1], b: [2], c: [3] } |> select(:a, :c)
    let df = frame_literal(vec![
        ("a", vec![lit_int(1)]),
        ("b", vec![lit_int(2)]),
        ("c", vec![lit_int(3)]),
    ]);
    let select = df_verb(
        DfVerbKind::Select,
        DfVerbArgs::Select(vec![sp("a".into()), sp("c".into())]),
    );
    let expr = df_pipe(df, select);
    let mut env = TypeEnv::new();
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
        "select should not produce errors, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            assert_eq!(row.fields.len(), 2, "select should restrict to 2 columns");
            assert!(row.fields.iter().any(|(l, _)| l.as_str() == "a"));
            assert!(row.fields.iter().any(|(l, _)| l.as_str() == "c"));
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_df_verb_sort_preserves_schema() {
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let sort = df_verb(
        DfVerbKind::Sort,
        DfVerbArgs::Sort {
            columns: vec![sp("x".into())],
            descending: false,
            nulls_first: false,
        },
    );
    let expr = df_pipe(df, sort);
    let mut env = TypeEnv::new();
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

    assert!(!unifier.has_errors(), "sort should not produce errors");
    assert!(matches!(&ty, Type::DataFrame(_)));
}

#[test]
fn infer_df_verb_distinct_preserves_schema() {
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let distinct = df_verb(DfVerbKind::Distinct, DfVerbArgs::Distinct);
    let expr = df_pipe(df, distinct);
    let mut env = TypeEnv::new();
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

    assert!(!unifier.has_errors(), "distinct should not produce errors");
    assert!(matches!(&ty, Type::DataFrame(_)));
}

#[test]
fn infer_df_verb_drop_removes_column() {
    // frame { a: [1], b: [2] } |> drop(:b)
    let df = frame_literal(vec![("a", vec![lit_int(1)]), ("b", vec![lit_int(2)])]);
    let drop_verb = df_verb(DfVerbKind::Drop, DfVerbArgs::Drop(vec![sp("b".into())]));
    let expr = df_pipe(df, drop_verb);
    let mut env = TypeEnv::new();
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
        "drop should not produce errors, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            assert!(
                row.fields.iter().any(|(l, _)| l.as_str() == "a"),
                "should have 'a'"
            );
            assert!(
                !row.fields.iter().any(|(l, _)| l.as_str() == "b"),
                "should not have 'b'"
            );
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_df_verb_filter_unknown_column_error() {
    // filter on a column that doesn't exist
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(
            BinOp::Gt,
            col_atom("nonexistent"),
            col_lit_int(0),
        )),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "referencing nonexistent column should error"
    );
}

#[test]
fn infer_df_verb_chained_pipes() {
    // frame { a: [1], b: [2], c: [3] } |> filter(:a > 0) |> select(:a, :b)
    let df = frame_literal(vec![
        ("a", vec![lit_int(1)]),
        ("b", vec![lit_int(2)]),
        ("c", vec![lit_int(3)]),
    ]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Gt, col_atom("a"), col_lit_int(0))),
    );
    let select = df_verb(
        DfVerbKind::Select,
        DfVerbArgs::Select(vec![sp("a".into()), sp("b".into())]),
    );
    let expr = df_pipe(df_pipe(df, filter), select);
    let mut env = TypeEnv::new();
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
        "chained pipes should not error, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            assert_eq!(row.fields.len(), 2, "select should restrict to 2 columns");
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

// -- Summarize type inference --

#[test]
fn infer_summarize_sum_returns_column_type() {
    // frame { x: [1, 2, 3] } |> group_by(:x) |> summarize(total: sum(:x))
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2), lit_int(3)])]);
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("x".into())]),
    );
    let summarize = df_verb(
        DfVerbKind::Summarize,
        DfVerbArgs::Summarize(vec![DfColAssignment::Named(
            sp("total".into()),
            col_call("sum", vec![col_atom("x")]),
        )]),
    );
    let expr = df_pipe(df_pipe(df, group), summarize);
    let mut env = TypeEnv::new();
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
        "summarize should not error, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            // Group key 'x' should appear in result
            let x = row.fields.iter().find(|(l, _)| l.as_str() == "x");
            assert!(x.is_some(), "should have group key 'x' column");
            assert_eq!(x.unwrap().1, Type::Int, "group key 'x' should be Int");
            let total = row.fields.iter().find(|(l, _)| l.as_str() == "total");
            assert!(total.is_some(), "should have 'total' column");
            // sum always returns nullable (empty group → null)
            assert_eq!(
                total.unwrap().1,
                Type::Option(Box::new(Type::Int)),
                "sum(:x) where x:Int should return Int?"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_summarize_count_returns_int() {
    // frame { x: [1, 2] } |> group_by(:x) |> summarize(n: count(:x))
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2)])]);
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("x".into())]),
    );
    let summarize = df_verb(
        DfVerbKind::Summarize,
        DfVerbArgs::Summarize(vec![DfColAssignment::Named(
            sp("n".into()),
            col_call("count", vec![col_atom("x")]),
        )]),
    );
    let expr = df_pipe(df_pipe(df, group), summarize);
    let mut env = TypeEnv::new();
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
        "count should not error, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let x = row.fields.iter().find(|(l, _)| l.as_str() == "x");
            assert!(x.is_some(), "should have group key 'x' column");
            let n = row.fields.iter().find(|(l, _)| l.as_str() == "n");
            assert!(n.is_some(), "should have 'n' column");
            assert_eq!(n.unwrap().1, Type::Int, "count should return Int");
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_summarize_mean_returns_float() {
    // frame { x: [1, 2] } |> group_by(:x) |> summarize(avg_x: mean(:x))
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2)])]);
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("x".into())]),
    );
    let summarize = df_verb(
        DfVerbKind::Summarize,
        DfVerbArgs::Summarize(vec![DfColAssignment::Named(
            sp("avg_x".into()),
            col_call("mean", vec![col_atom("x")]),
        )]),
    );
    let expr = df_pipe(df_pipe(df, group), summarize);
    let mut env = TypeEnv::new();
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
        "mean should not error, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let x = row.fields.iter().find(|(l, _)| l.as_str() == "x");
            assert!(x.is_some(), "should have group key 'x' column");
            let avg_x = row.fields.iter().find(|(l, _)| l.as_str() == "avg_x");
            assert!(avg_x.is_some(), "should have 'avg_x' column");
            // mean always returns nullable (empty group → null)
            assert_eq!(
                avg_x.unwrap().1,
                Type::Option(Box::new(Type::Float)),
                "mean should return Float?"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_summarize_sum_on_decimal_preserves_decimal_type() {
    // frame { x: [1, 2] } |> cast(:x, Decimal(18, 2)) |> group_by(:x) |> summarize(total: sum(:x))
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2)])]);
    let cast = df_verb(
        DfVerbKind::Cast,
        DfVerbArgs::Cast(sp("x".into()), sp("Decimal(18, 2)".into())),
    );
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("x".into())]),
    );
    let summarize = df_verb(
        DfVerbKind::Summarize,
        DfVerbArgs::Summarize(vec![DfColAssignment::Named(
            sp("total".into()),
            col_call("sum", vec![col_atom("x")]),
        )]),
    );
    let expr = df_pipe(df_pipe(df_pipe(df, cast), group), summarize);
    let mut env = TypeEnv::new();
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
        "decimal summarize(sum) should not error, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let x = row.fields.iter().find(|(l, _)| l.as_str() == "x");
            assert_eq!(
                x.map(|(_, t)| t.clone()),
                Some(decimal(18, 2)),
                "group key x should be Decimal(18, 2)"
            );
            let total = row.fields.iter().find(|(l, _)| l.as_str() == "total");
            assert_eq!(
                total.map(|(_, t)| t.clone()),
                Some(Type::Option(Box::new(decimal(18, 2)))),
                "sum(:x) where x:Decimal(18,2) should return Decimal(18,2)?"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_summarize_mean_on_decimal_returns_float() {
    // frame { x: [1, 2] } |> cast(:x, Decimal(18, 2)) |> group_by(:x) |> summarize(avg_x: mean(:x))
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2)])]);
    let cast = df_verb(
        DfVerbKind::Cast,
        DfVerbArgs::Cast(sp("x".into()), sp("Decimal(18, 2)".into())),
    );
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("x".into())]),
    );
    let summarize = df_verb(
        DfVerbKind::Summarize,
        DfVerbArgs::Summarize(vec![DfColAssignment::Named(
            sp("avg_x".into()),
            col_call("mean", vec![col_atom("x")]),
        )]),
    );
    let expr = df_pipe(df_pipe(df_pipe(df, cast), group), summarize);
    let mut env = TypeEnv::new();
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
        "decimal summarize(mean) should not error, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let avg_x = row.fields.iter().find(|(l, _)| l.as_str() == "avg_x");
            assert_eq!(
                avg_x.map(|(_, t)| t.clone()),
                Some(Type::Option(Box::new(Type::Float))),
                "mean(:x) where x:Decimal(18,2) should return Float?"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_summarize_stddev_string_column_fails_numeric_bound() {
    let df = frame_literal(vec![("name", vec![lit_str("a"), lit_str("b")])]);
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("name".into())]),
    );
    let summarize = df_verb(
        DfVerbKind::Summarize,
        DfVerbArgs::Summarize(vec![DfColAssignment::Named(
            sp("s".into()),
            col_call("stddev", vec![col_atom("name")]),
        )]),
    );
    let expr = df_pipe(df_pipe(df, group), summarize);

    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    unifier.check_trait_bounds(&traits);
    assert!(
        unifier.has_errors(),
        "stddev over String should fail Numeric bound"
    );
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("Numeric")),
        "expected Numeric bound error, got: {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_summarize_stddev_int_column_passes_numeric_bound() {
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2), lit_int(3)])]);
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("x".into())]),
    );
    let summarize = df_verb(
        DfVerbKind::Summarize,
        DfVerbArgs::Summarize(vec![DfColAssignment::Named(
            sp("s".into()),
            col_call("stddev", vec![col_atom("x")]),
        )]),
    );
    let expr = df_pipe(df_pipe(df, group), summarize);

    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let mut traits = TraitRegistry::new();
    traits
        .register_trait(&make_trait_def("Numeric", vec![]), &records)
        .unwrap();
    traits
        .register_trait_impl(&make_impl_block("Numeric", "Int", vec![]))
        .unwrap();

    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    unifier.check_trait_bounds(&traits);
    assert!(
        !unifier.has_errors(),
        "stddev over Int should satisfy Numeric bound: {:?}",
        unifier.errors()
    );
}

// -- Capture type inference --

fn col_capture(name: &str) -> ColExpr {
    sp(ColExprKind::Capture(name.to_string()))
}

fn col_none() -> ColExpr {
    sp(ColExprKind::None)
}

fn col_lit_float(f: f64) -> ColExpr {
    sp(ColExprKind::Lit(Lit::Float(f)))
}

fn col_cond(arms: Vec<ColCondArm>) -> ColExpr {
    sp(ColExprKind::Cond { arms })
}

fn col_cond_arm(condition: ColExpr, body: ColExpr) -> ColCondArm {
    ColCondArm {
        span: condition.span.merge(body.span),
        condition: Box::new(condition),
        body: Box::new(body),
    }
}

fn col_cond_wildcard_arm(body: ColExpr) -> ColCondArm {
    let wildcard = sp(ColExprKind::Wildcard);
    ColCondArm {
        span: wildcard.span.merge(body.span),
        condition: Box::new(wildcard),
        body: Box::new(body),
    }
}

#[test]
fn infer_capture_resolves_type_from_scope() {
    // let threshold = 10
    // frame { x: [1, 2, 3] } |> filter(:x > $threshold)
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2), lit_int(3)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(
            BinOp::Gt,
            col_atom("x"),
            col_capture("threshold"),
        )),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    env.bind("threshold".into(), TypeScheme::mono(Type::Int));
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        !unifier.has_errors(),
        "capture from scope should not error, got: {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_mutate_cond_in_column_expr() {
    // frame { score: [95, 75, 50] } |> mutate(grade: cond { :score > 90 -> "A", :score > 70 -> "B", _ -> "C" })
    let df = frame_literal(vec![("score", vec![lit_int(95), lit_int(75), lit_int(50)])]);
    let grade_expr = col_cond(vec![
        col_cond_arm(
            col_binop(BinOp::Gt, col_atom("score"), col_lit_int(90)),
            col_lit_str("A"),
        ),
        col_cond_arm(
            col_binop(BinOp::Gt, col_atom("score"), col_lit_int(70)),
            col_lit_str("B"),
        ),
        col_cond_wildcard_arm(col_lit_str("C")),
    ]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(sp("grade".into()), grade_expr)]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "cond mutate should type-check: {:?}",
        unifier.errors()
    );
    if let Type::DataFrame(inner) = ty {
        if let Type::AnonRecord(row) = *inner {
            let grade = row
                .fields
                .iter()
                .find(|(label, _)| label.as_str() == "grade")
                .map(|(_, ty)| ty.clone());
            assert_eq!(grade, Some(Type::String));
        } else {
            panic!("expected DataFrame(AnonRecord), got {inner:?}");
        }
    } else {
        panic!("expected DataFrame type, got {ty:?}");
    }
}

#[test]
fn infer_mutate_cond_requires_catch_all() {
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let bad_cond = col_cond(vec![col_cond_arm(
        col_binop(BinOp::Gt, col_atom("x"), col_lit_int(0)),
        col_lit_int(1),
    )]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(sp("y".into()), bad_cond)]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors(), "expected non-exhaustive cond error");
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("non-exhaustive cond")),
        "expected non-exhaustive cond diagnostic, got {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_capture_undefined_errors() {
    // frame { x: [1] } |> filter(:x > $missing)
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Gt, col_atom("x"), col_capture("missing"))),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "undefined capture should produce error"
    );
}

#[test]
fn infer_capture_type_mismatch_errors() {
    // let threshold = "hello"
    // frame { x: [1] } |> filter(:x > $threshold)
    // :x is Int, $threshold is String — should error on comparison
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(
            BinOp::Gt,
            col_atom("x"),
            col_capture("threshold"),
        )),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    env.bind("threshold".into(), TypeScheme::mono(Type::String));
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "Int vs String comparison should error"
    );
}

// -- Rename type inference --

#[test]
fn infer_rename_updates_schema() {
    // frame { x: [1], y: [2] } |> rename(z: :x) |> filter(:z > 0)
    let df = frame_literal(vec![("x", vec![lit_int(1)]), ("y", vec![lit_int(2)])]);
    let rename = df_verb(
        DfVerbKind::Rename,
        DfVerbArgs::Rename(vec![(sp("z".into()), sp("x".into()))]),
    );
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Gt, col_atom("z"), col_lit_int(0))),
    );
    let expr = df_pipe(df_pipe(df, rename), filter);
    let mut env = TypeEnv::new();
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
        "rename + filter on new name should work, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let has_z = row.fields.iter().any(|(l, _)| l.as_str() == "z");
            let has_x = row.fields.iter().any(|(l, _)| l.as_str() == "x");
            assert!(has_z, "should have column 'z' after rename");
            assert!(!has_x, "should NOT have column 'x' after rename");
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

// -- Scalar function type inference --

#[test]
fn infer_is_none_returns_bool() {
    // frame { x: [1] } |> filter(is_none(:x))
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_call("is_none", vec![col_atom("x")])),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    // is_none returns Bool, which is valid for filter — no error
    assert!(
        !unifier.has_errors(),
        "is_none(:x) should return Bool, got: {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_lower_requires_string() {
    // frame { name: ["Alice"] } |> mutate(lower_name: lower(:name))
    let df = frame_literal(vec![(
        "name",
        vec![sp(ExprKind::Lit(Lit::String("Alice".into())))],
    )]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("lower_name".into()),
            col_call("lower", vec![col_atom("name")]),
        )]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "lower(:name) on String column should work, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let lower_name = row.fields.iter().find(|(l, _)| l.as_str() == "lower_name");
            assert!(lower_name.is_some(), "should have 'lower_name' column");
            assert_eq!(
                lower_name.unwrap().1,
                Type::String,
                "lower should return String"
            );
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_coalesce_unifies_args() {
    // frame { x: [1] } |> mutate(safe: coalesce(:x, 0))
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("safe".into()),
            col_call("coalesce", vec![col_atom("x"), col_lit_int(0)]),
        )]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "coalesce should not error, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let safe = row.fields.iter().find(|(l, _)| l.as_str() == "safe");
            assert!(safe.is_some(), "should have 'safe' column");
            assert_eq!(
                safe.unwrap().1,
                Type::Int,
                "coalesce(:x, 0) should return Int"
            );
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_coalesce_two_args_uses_non_nullable_fallback() {
    // frame { x: [None, 1], y: [2, 4] } |> mutate(safe: coalesce(:x, :y))
    let df = frame_literal(vec![
        ("x", vec![none_expr(), lit_int(1)]),
        ("y", vec![lit_int(2), lit_int(4)]),
    ]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("safe".into()),
            col_call("coalesce", vec![col_atom("x"), col_atom("y")]),
        )]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "variadic coalesce should not error, got: {:?}",
        unifier.errors()
    );
    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let safe = row.fields.iter().find(|(l, _)| l.as_str() == "safe");
            assert!(safe.is_some(), "should have 'safe' column");
            assert_eq!(
                safe.unwrap().1,
                Type::Int,
                "coalesce(:x, :y) should return Int (non-nullable fallback present)"
            );
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_na_if_returns_nullable_column() {
    // frame { x: [1, -1, 3] } |> mutate(cleaned: na_if(:x, -1))
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(-1), lit_int(3)])]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("cleaned".into()),
            col_call("na_if", vec![col_atom("x"), col_lit_int(-1)]),
        )]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "na_if should not error, got: {:?}",
        unifier.errors()
    );
    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let cleaned = row.fields.iter().find(|(l, _)| l.as_str() == "cleaned");
            assert!(cleaned.is_some(), "should have 'cleaned' column");
            assert!(
                matches!(cleaned.unwrap().1, Type::Option(_)),
                "na_if(:x, -1) should return nullable Int"
            );
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_window_rank_and_row_number_types() {
    // frame { x: [1, 2, 3] } |> mutate(r: rank(:x), rn: row_number())
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2), lit_int(3)])]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![
            DfColAssignment::Named(sp("r".into()), col_call("rank", vec![col_atom("x")])),
            DfColAssignment::Named(sp("rn".into()), col_call("row_number", vec![])),
        ]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "window ranking functions should type-check, got: {:?}",
        unifier.errors()
    );
    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let r = row.fields.iter().find(|(l, _)| l.as_str() == "r");
            let rn = row.fields.iter().find(|(l, _)| l.as_str() == "rn");
            assert_eq!(r.map(|(_, t)| t), Some(&Type::Int));
            assert_eq!(rn.map(|(_, t)| t), Some(&Type::Int));
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_lag_and_cumsum_are_nullable() {
    // frame { x: [1, 2, 3] } |> mutate(prev: lag(:x, 1, 0), running: cumsum(:x))
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2), lit_int(3)])]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![
            DfColAssignment::Named(
                sp("prev".into()),
                col_call("lag", vec![col_atom("x"), col_lit_int(1), col_lit_int(0)]),
            ),
            DfColAssignment::Named(
                sp("running".into()),
                col_call("cumsum", vec![col_atom("x")]),
            ),
        ]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "lag/cumsum should type-check, got: {:?}",
        unifier.errors()
    );
    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let prev = row.fields.iter().find(|(l, _)| l.as_str() == "prev");
            let running = row.fields.iter().find(|(l, _)| l.as_str() == "running");
            assert!(
                matches!(prev.map(|(_, t)| t), Some(Type::Option(_))),
                "lag should produce nullable output"
            );
            assert!(
                matches!(running.map(|(_, t)| t), Some(Type::Option(_))),
                "cumsum should produce nullable output"
            );
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_mutate_across_explicit_columns_typechecks() {
    let df = frame_literal(vec![
        ("x", vec![lit_int(1), lit_int(2)]),
        ("y", vec![lit_int(3), lit_int(4)]),
    ]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Across(DfAcrossSpec {
            selector: DfAcrossSelector::Columns(vec![sp("x".into()), sp("y".into())]),
            template: col_call("coalesce", vec![col_atom("col"), col_lit_int(0)]),
        })]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "mutate across explicit columns should type-check: {:?}",
        unifier.errors()
    );
    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            assert!(row.fields.iter().any(|(l, _)| l.as_str() == "x"));
            assert!(row.fields.iter().any(|(l, _)| l.as_str() == "y"));
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame");
    }
}

#[test]
fn infer_mutate_across_selector_numeric_skips_non_numeric() {
    let df = frame_literal(vec![
        ("x", vec![lit_int(1), lit_int(2)]),
        ("name", vec![lit_str("a"), lit_str("b")]),
    ]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Across(DfAcrossSpec {
            selector: DfAcrossSelector::Selector(sp("Numeric".into())),
            template: col_call("coalesce", vec![col_atom("col"), col_lit_int(0)]),
        })]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "mutate across Numeric should type-check: {:?}",
        unifier.errors()
    );
    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            assert!(row.fields.iter().any(|(l, _)| l.as_str() == "x"));
            assert!(row.fields.iter().any(|(l, _)| l.as_str() == "name"));
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame");
    }
}

#[test]
fn infer_mutate_across_unknown_selector_errors() {
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2)])]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Across(DfAcrossSpec {
            selector: DfAcrossSelector::Selector(sp("NopeTrait".into())),
            template: col_atom("col"),
        })]),
    );
    let expr = df_pipe(df, mutate);
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
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.message.contains("unknown across selector")),
        "expected unknown selector diagnostic, got: {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_summarize_across_numeric_typechecks() {
    let df = frame_literal(vec![
        (
            "region",
            vec![lit_str("east"), lit_str("west"), lit_str("east")],
        ),
        ("x", vec![lit_int(1), lit_int(2), lit_int(3)]),
    ]);
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("region".into())]),
    );
    let summarize = df_verb(
        DfVerbKind::Summarize,
        DfVerbArgs::Summarize(vec![DfColAssignment::Across(DfAcrossSpec {
            selector: DfAcrossSelector::Selector(sp("Numeric".into())),
            template: col_call("sum", vec![col_atom("col")]),
        })]),
    );
    let expr = df_pipe(df_pipe(df, group), summarize);
    let mut env = TypeEnv::new();
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
        "summarize across Numeric should type-check: {:?}",
        unifier.errors()
    );
    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            assert!(row.fields.iter().any(|(l, _)| l.as_str() == "region"));
            assert!(row.fields.iter().any(|(l, _)| l.as_str() == "x"));
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame");
    }
}

// -- Cast verb type inference --

#[test]
fn infer_group_by_returns_grouped_frame() {
    // frame { x: [1], y: [2] } |> group_by(:x)
    let df = frame_literal(vec![("x", vec![lit_int(1)]), ("y", vec![lit_int(2)])]);
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("x".into())]),
    );
    let expr = df_pipe(df, group);
    let mut env = TypeEnv::new();
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
        "group_by should not error, got: {:?}",
        unifier.errors()
    );
    assert!(
        matches!(&ty, Type::GroupedFrame { .. }),
        "expected GroupedFrame, got {:?}",
        ty
    );
}

#[test]
fn infer_summarize_without_group_by_errors() {
    // frame { x: [1] } |> summarize(total: sum(:x)) — no group_by!
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let summarize = df_verb(
        DfVerbKind::Summarize,
        DfVerbArgs::Summarize(vec![DfColAssignment::Named(
            sp("total".into()),
            col_call("sum", vec![col_atom("x")]),
        )]),
    );
    let expr = df_pipe(df, summarize);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "summarize without group_by should error"
    );
}

#[test]
fn infer_filter_on_grouped_frame_errors() {
    // frame { x: [1] } |> group_by(:x) |> filter(:x > 0)
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("x".into())]),
    );
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Gt, col_atom("x"), col_lit_int(0))),
    );
    let expr = df_pipe(df_pipe(df, group), filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(unifier.has_errors(), "filter on GroupedFrame should error");
}

#[test]
fn infer_cast_changes_column_type() {
    // frame { x: [1] } |> cast(:x, Float)
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let cast = df_verb(
        DfVerbKind::Cast,
        DfVerbArgs::Cast(sp("x".into()), sp("Float".into())),
    );
    let expr = df_pipe(df, cast);
    let mut env = TypeEnv::new();
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
        "cast should succeed, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let x = row.fields.iter().find(|(l, _)| l.as_str() == "x");
            assert!(x.is_some(), "should still have column 'x'");
            assert_eq!(
                x.unwrap().1,
                Type::Float,
                "x should now be Float after cast"
            );
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_cast_decimal_target_changes_column_type() {
    // frame { x: [1] } |> cast(:x, Decimal(18, 2))
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let cast = df_verb(
        DfVerbKind::Cast,
        DfVerbArgs::Cast(sp("x".into()), sp("Decimal(18, 2)".into())),
    );
    let expr = df_pipe(df, cast);
    let mut env = TypeEnv::new();
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
        "cast to Decimal should succeed, got: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let x = row.fields.iter().find(|(l, _)| l.as_str() == "x");
            assert!(x.is_some(), "should still have column 'x'");
            assert_eq!(
                x.unwrap().1,
                Type::Decimal {
                    precision: Dim::Known(18),
                    scale: Dim::Known(2),
                },
                "x should now be Decimal(18, 2) after cast"
            );
        } else {
            panic!("expected AnonRecord");
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_cast_unknown_type_errors() {
    // frame { x: [1] } |> cast(:x, Banana)
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let cast = df_verb(
        DfVerbKind::Cast,
        DfVerbArgs::Cast(sp("x".into()), sp("Banana".into())),
    );
    let expr = df_pipe(df, cast);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(unifier.has_errors(), "cast to unknown type should error");
}

// ---------------------------------------------------------------------------
// Join / LeftJoin verb type inference
// ---------------------------------------------------------------------------

#[test]
fn infer_inner_join() {
    // frame { x: [1], y: [2] } |> join(frame { x: [1], z: [3] }, on: :x)
    // Result: DataFrame(#{ x: Int, y: Int, z: Int })
    let left = frame_literal(vec![("x", vec![lit_int(1)]), ("y", vec![lit_int(2)])]);
    let right = frame_literal(vec![("x", vec![lit_int(1)]), ("z", vec![lit_int(3)])]);
    let join = df_verb(
        DfVerbKind::Join,
        DfVerbArgs::Join {
            right: Box::new(right),
            on: vec![sp("x".into())],
            how: None,
        },
    );
    let expr = df_pipe(left, join);
    let mut env = TypeEnv::new();
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
        "inner join should not error: {:?}",
        unifier.errors()
    );
    match &ty {
        Type::DataFrame(inner) => match inner.as_ref() {
            Type::AnonRecord(row) => {
                assert_eq!(row.fields.len(), 3);
                let names: Vec<&str> = row.fields.iter().map(|(l, _)| l.as_str()).collect();
                assert!(names.contains(&"x"));
                assert!(names.contains(&"y"));
                assert!(names.contains(&"z"));
            }
            _ => panic!("expected AnonRecord, got {inner}"),
        },
        _ => panic!("expected DataFrame, got {ty}"),
    }
}

#[test]
fn infer_join_how_left_wraps_right_in_option() {
    // frame { x: [1], y: [2] } |> join(frame { x: [1], z: [3] }, on: :x, how: :left)
    // Result: DataFrame(#{ x: Int, y: Int, z: Int? })
    let left = frame_literal(vec![("x", vec![lit_int(1)]), ("y", vec![lit_int(2)])]);
    let right = frame_literal(vec![("x", vec![lit_int(1)]), ("z", vec![lit_int(3)])]);
    let join = df_verb(
        DfVerbKind::Join,
        DfVerbArgs::Join {
            right: Box::new(right),
            on: vec![sp("x".into())],
            how: Some(sp("left".into())),
        },
    );
    let expr = df_pipe(left, join);
    let mut env = TypeEnv::new();
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
        "left join should not error: {:?}",
        unifier.errors()
    );
    match &ty {
        Type::DataFrame(inner) => match inner.as_ref() {
            Type::AnonRecord(row) => {
                let z_ty = row
                    .fields
                    .iter()
                    .find(|(l, _)| l.as_str() == "z")
                    .map(|(_, t)| t);
                assert!(
                    matches!(z_ty, Some(Type::Option(_))),
                    "right non-key column `z` should be Option, got {:?}",
                    z_ty
                );
            }
            _ => panic!("expected AnonRecord, got {inner}"),
        },
        _ => panic!("expected DataFrame, got {ty}"),
    }
}

#[test]
fn infer_join_how_cross_allows_empty_on() {
    // frame { x: [1], y: [2] } |> join(frame { z: [3] }, how: :cross)
    let left = frame_literal(vec![("x", vec![lit_int(1)]), ("y", vec![lit_int(2)])]);
    let right = frame_literal(vec![("z", vec![lit_int(3)])]);
    let join = df_verb(
        DfVerbKind::Join,
        DfVerbArgs::Join {
            right: Box::new(right),
            on: vec![],
            how: Some(sp("cross".into())),
        },
    );
    let expr = df_pipe(left, join);
    let mut env = TypeEnv::new();
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
        "cross join without `on:` should not error: {:?}",
        unifier.errors()
    );
    match &ty {
        Type::DataFrame(inner) => match inner.as_ref() {
            Type::AnonRecord(row) => {
                assert_eq!(row.fields.len(), 3);
                let names: Vec<&str> = row.fields.iter().map(|(l, _)| l.as_str()).collect();
                assert!(names.contains(&"x"));
                assert!(names.contains(&"y"));
                assert!(names.contains(&"z"));
            }
            _ => panic!("expected AnonRecord, got {inner}"),
        },
        _ => panic!("expected DataFrame, got {ty}"),
    }
}

#[test]
fn infer_join_how_cross_rejects_on_keys() {
    let left = frame_literal(vec![("x", vec![lit_int(1)]), ("y", vec![lit_int(2)])]);
    let right = frame_literal(vec![("x", vec![lit_int(1)]), ("z", vec![lit_int(3)])]);
    let join = df_verb(
        DfVerbKind::Join,
        DfVerbArgs::Join {
            right: Box::new(right),
            on: vec![sp("x".into())],
            how: Some(sp("cross".into())),
        },
    );
    let expr = df_pipe(left, join);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(unifier.has_errors(), "cross join with `on:` should error");
}

#[test]
fn infer_join_overlapping_non_key_errors() {
    // frame { x: [1], y: [2] } |> join(frame { x: [1], y: [3] }, on: :x)
    // Should error: both have non-key column `y`
    let left = frame_literal(vec![("x", vec![lit_int(1)]), ("y", vec![lit_int(2)])]);
    let right = frame_literal(vec![("x", vec![lit_int(1)]), ("y", vec![lit_int(3)])]);
    let join = df_verb(
        DfVerbKind::Join,
        DfVerbArgs::Join {
            right: Box::new(right),
            on: vec![sp("x".into())],
            how: None,
        },
    );
    let expr = df_pipe(left, join);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "overlapping non-key column should error"
    );
}

#[test]
fn infer_join_missing_key_in_right_errors() {
    // frame { x: [1], y: [2] } |> join(frame { z: [1] }, on: :x)
    // Should error: key `x` not in right
    let left = frame_literal(vec![("x", vec![lit_int(1)]), ("y", vec![lit_int(2)])]);
    let right = frame_literal(vec![("z", vec![lit_int(1)])]);
    let join = df_verb(
        DfVerbKind::Join,
        DfVerbArgs::Join {
            right: Box::new(right),
            on: vec![sp("x".into())],
            how: None,
        },
    );
    let expr = df_pipe(left, join);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(unifier.has_errors(), "missing key in right should error");
}

// ---------------------------------------------------------------------------
// Actor operations
// ---------------------------------------------------------------------------

/// Create a TraitRegistry with Actor trait and impls for common primitive types.
/// Used by spawn tests that need to pass the Actor trait check.
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
    traits.register_trait(&actor_trait, &records).unwrap();
    // Register Actor impls for types used in spawn tests
    for type_name in ["Int", "String", "Bool", "Float", "Unit", "Tuple"] {
        if type_name == "Tuple" {
            traits.register_type_owner(type_name, "repl:");
        }
        let impl_block = kea_ast::ImplBlock {
            trait_name: sp("Actor".to_string()),
            type_name: sp(type_name.to_string()),
            type_params: vec![],
            methods: vec![],
            control_type: None,
            where_clause: vec![],
        };
        traits.register_trait_impl(&impl_block).unwrap();
    }
    traits
}

fn spawn_expr(value: Expr) -> Expr {
    sp(ExprKind::Spawn {
        value: Box::new(value),
        config: None,
    })
}

fn await_expr(value: Expr, safe: bool) -> Expr {
    sp(ExprKind::Await {
        expr: Box::new(value),
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

#[test]
fn infer_spawn_returns_actor_type() {
    // let x = 1; spawn x → Actor(Int)
    let expr = block(vec![let_bind("x", lit_int(1)), spawn_expr(var("x"))]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors());
    assert!(matches!(ty, Type::Actor(ref inner) if **inner == Type::Int));
}

#[test]
fn infer_spawn_string() {
    // spawn "hello" → Actor(String)
    let expr = spawn_expr(lit_str("hello"));
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors());
    assert!(matches!(ty, Type::Actor(ref inner) if **inner == Type::String));
}

#[test]
fn infer_send_returns_unit() {
    // let a = spawn 42; send(a, :inc) → ()
    let inner = block(vec![
        let_bind("a", spawn_expr(lit_int(42))),
        actor_send(var("a"), "inc", vec![]),
    ]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &inner,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors());
    assert_eq!(ty, Type::Unit);
}

#[test]
fn infer_send_with_args_returns_unit() {
    // let a = spawn 42; send(a, :add, 1, 2) → ()
    let inner = block(vec![
        let_bind("a", spawn_expr(lit_int(42))),
        actor_send(var("a"), "add", vec![lit_int(1), lit_int(2)]),
    ]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &inner,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors());
    assert_eq!(ty, Type::Unit);
}

#[test]
fn infer_try_send_returns_result_actor_error() {
    let inner = block(vec![
        let_bind("a", spawn_expr(lit_int(42))),
        actor_try_send(var("a"), "inc", vec![]),
    ]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &inner,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors());
    assert_eq!(
        ty,
        Type::Result(
            Box::new(Type::Unit),
            Box::new(kea_types::builtin_error_sum_type("ActorError").expect("builtin error type"))
        )
    );
}

#[test]
fn infer_try_send_on_non_actor_errors() {
    let expr = actor_try_send(lit_int(42), "inc", vec![]);
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
    assert!(unifier.has_errors());
}

#[test]
fn infer_call_safe_returns_result_actor_error() {
    // let a = spawn 42; call?(a, :get) → Result(T, ActorError)
    let inner = block(vec![
        let_bind("a", spawn_expr(lit_int(42))),
        actor_call_safe(var("a"), "get", vec![]),
    ]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &inner,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors());
    match ty {
        Type::Result(_, ref err) => assert_eq!(
            **err,
            kea_types::builtin_error_sum_type("ActorError").expect("builtin error type")
        ),
        other => panic!("expected Result(_, ActorError) for call?, got {other}"),
    }
}

#[test]
fn infer_send_on_non_actor_errors() {
    // send(42, :inc) → error (42 is Int, not Actor)
    let expr = actor_send(lit_int(42), "inc", vec![]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors(), "send on non-actor should error");
}

#[test]
fn infer_call_on_non_actor_errors() {
    // call("hello", :get) → error
    let expr = actor_call(lit_str("hello"), "get", vec![]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(unifier.has_errors(), "call on non-actor should error");
}

#[test]
fn infer_spawn_then_send_then_call() {
    // let c = actor
    // let _ = send(a, :inc)
    // call(a, :get) returns the value directly
    let inner = block(vec![
        let_bind("_", actor_send(var("c"), "inc", vec![])),
        actor_call(var("c"), "get", vec![]),
    ]);
    let (mut env, records, traits) = setup_actor_protocol_test();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &inner,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors());
    assert_eq!(ty, Type::Int);
}

#[test]
fn infer_spawn_preserves_inner_type() {
    // spawn #(1, "hello") → Actor(#(Int, String))
    let tuple = sp(ExprKind::Tuple(vec![lit_int(1), lit_str("hello")]));
    let expr = spawn_expr(tuple);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors());
    match ty {
        Type::Actor(ref inner) => match inner.as_ref() {
            Type::Tuple(elems) => {
                assert_eq!(elems.len(), 2);
                assert_eq!(elems[0], Type::Int);
                assert_eq!(elems[1], Type::String);
            }
            other => panic!("expected Tuple inside Actor, got {other}"),
        },
        other => panic!("expected Actor, got {other}"),
    }
}

// ---------------------------------------------------------------------------
// Sendable enforcement
// ---------------------------------------------------------------------------

#[test]
fn infer_spawn_closure_not_sendable() {
    // spawn |x| x → error (closures are not Sendable)
    let expr = spawn_expr(lambda(&["x"], var("x")));
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "spawning a closure should produce a Sendable error"
    );
    let msg = format!("{:?}", unifier.errors);
    assert!(
        msg.contains("Sendable"),
        "error should mention Sendable, got: {msg}"
    );
}

#[test]
fn infer_spawn_function_not_sendable() {
    // spawn (|x| x) → error (Function type is not Sendable)
    // Same as above — lambdas infer as Function type which is not Sendable.
    let expr = spawn_expr(lambda(&["a", "b"], lit_int(1)));
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "spawning a function should produce a Sendable error"
    );
}

#[test]
fn infer_send_closure_arg_not_sendable() {
    // let a = spawn 42; send(a, :method, |x| x) → error (closure arg not Sendable)
    let inner = block(vec![
        let_bind("a", spawn_expr(lit_int(42))),
        actor_send(var("a"), "method", vec![lambda(&["x"], var("x"))]),
    ]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &inner,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        unifier.has_errors(),
        "sending a closure arg should produce a Sendable error"
    );
    let msg = format!("{:?}", unifier.errors);
    assert!(
        msg.contains("Sendable"),
        "error should mention Sendable, got: {msg}"
    );
}

#[test]
fn infer_call_closure_arg_not_sendable() {
    // let a = spawn 42; call(a, :method, |x| x) → error (closure arg not Sendable)
    let inner = block(vec![
        let_bind("a", spawn_expr(lit_int(42))),
        actor_call(var("a"), "method", vec![lambda(&["x"], var("x"))]),
    ]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &inner,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(
        unifier.has_errors(),
        "calling with a closure arg should produce a Sendable error"
    );
    let msg = format!("{:?}", unifier.errors);
    assert!(
        msg.contains("Sendable"),
        "error should mention Sendable, got: {msg}"
    );
}

#[test]
fn infer_spawn_int_is_sendable() {
    // spawn 42 → Actor(Int), no errors
    let expr = spawn_expr(lit_int(42));
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors(), "spawning an Int should be fine");
    assert!(matches!(ty, Type::Actor(ref inner) if **inner == Type::Int));
}

#[test]
fn infer_spawn_int_is_sendable_without_sendable_impl_when_trait_exists() {
    // Structural sendability still applies when `Sendable` trait exists but
    // no explicit impl matches.
    let expr = spawn_expr(lit_int(42));
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let mut traits = traits_with_actor();
    traits
        .register_trait(&make_trait_def("Sendable", vec![]), &records)
        .unwrap();
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
        "spawning Int should use structural sendability fallback"
    );
    assert!(matches!(ty, Type::Actor(ref inner) if **inner == Type::Int));
}

#[test]
fn infer_send_int_arg_is_sendable() {
    // let a = spawn 42; send(a, :add, 1) → Unit, no errors
    let inner = block(vec![
        let_bind("a", spawn_expr(lit_int(42))),
        actor_send(var("a"), "add", vec![lit_int(1)]),
    ]);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = traits_with_actor();
    let mut unifier = Unifier::new();
    let ty = infer_and_resolve(
        &inner,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );
    assert!(!unifier.has_errors(), "sending an Int arg should be fine");
    assert_eq!(ty, Type::Unit);
}

// ---------------------------------------------------------------------------
// Col(T) type boundary + nullable propagation + == None ban
// ---------------------------------------------------------------------------

#[test]
fn infer_col_expr_none_eq_banned() {
    // filter(:x == None) → compile error suggesting is_none()
    let df = frame_literal(vec![("x", vec![lit_int(1), none_expr(), lit_int(3)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Eq, col_atom("x"), col_none())),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(unifier.has_errors(), ":x == None should be a compile error");
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("is_none"),
        "error should suggest is_none(), got: {msg}"
    );
}

#[test]
fn infer_col_expr_none_neq_banned() {
    // filter(:x != None) → compile error suggesting is_some()
    let df = frame_literal(vec![("x", vec![lit_int(1), none_expr(), lit_int(3)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Neq, col_atom("x"), col_none())),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(unifier.has_errors(), ":x != None should be a compile error");
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("is_some"),
        "error should suggest is_some(), got: {msg}"
    );
}

#[test]
fn infer_col_expr_none_eq_reversed_banned() {
    // filter(None == :x) → also caught (None on left side)
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Eq, col_none(), col_atom("x"))),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(unifier.has_errors(), "None == :x should be caught too");
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("is_none"),
        "error should suggest is_none(), got: {msg}"
    );
}

#[test]
fn infer_col_expr_none_eq_nested_banned() {
    // filter((:x == None) or (:y > 1)) → caught in nested BinaryOp
    let df = frame_literal(vec![
        ("x", vec![lit_int(1), none_expr()]),
        ("y", vec![lit_int(2), lit_int(3)]),
    ]);
    let none_cmp = col_binop(BinOp::Eq, col_atom("x"), col_none());
    let gt_cmp = col_binop(BinOp::Gt, col_atom("y"), col_lit_int(1));
    let or_expr = col_binop(BinOp::Or, none_cmp, gt_cmp);
    let filter = df_verb(DfVerbKind::Filter, DfVerbArgs::Filter(or_expr));
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "nested :x == None should still be caught"
    );
    let msg = format!("{:?}", unifier.errors());
    assert!(
        msg.contains("is_none"),
        "error should suggest is_none(), got: {msg}"
    );
}

#[test]
fn infer_col_expr_nullable_arithmetic() {
    // frame { x: [1.0, None, 3.0] } |> mutate(y: :x + 1.0)
    // x is Float?, so y should be Float? in the output schema
    let df = frame_literal(vec![(
        "x",
        vec![lit_float(1.0), none_expr(), lit_float(3.0)],
    )]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("y".into()),
            col_binop(BinOp::Add, col_atom("x"), col_lit_float(1.0)),
        )]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "nullable arithmetic should work: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let y = row.fields.iter().find(|(l, _)| l.as_str() == "y");
            assert!(y.is_some(), "should have 'y' column");
            assert_eq!(
                y.unwrap().1,
                Type::Option(Box::new(Type::Float)),
                "y should be Float? (nullable propagated from x)"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_col_expr_nullable_comparison() {
    // frame { x: [1.0, None, 3.0] } |> filter(:x > 2.0)
    // x is Float?, comparison produces Bool?, filter accepts Bool?
    let df = frame_literal(vec![(
        "x",
        vec![lit_float(1.0), none_expr(), lit_float(3.0)],
    )]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Gt, col_atom("x"), col_lit_float(2.0))),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
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
        "filter with nullable comparison should work: {:?}",
        unifier.errors()
    );
    assert!(
        matches!(&ty, Type::DataFrame(_)),
        "expected DataFrame, got {:?}",
        ty
    );
}

#[test]
fn infer_col_expr_non_nullable_comparison() {
    // frame { x: [1.0, 2.0] } |> mutate(flag: :x > 1.5)
    // x is Float (not nullable), so flag should be Bool (not Bool?)
    let df = frame_literal(vec![("x", vec![lit_float(1.0), lit_float(2.0)])]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("flag".into()),
            col_binop(BinOp::Gt, col_atom("x"), col_lit_float(1.5)),
        )]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "non-nullable comparison should work: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let flag = row.fields.iter().find(|(l, _)| l.as_str() == "flag");
            assert!(flag.is_some(), "should have 'flag' column");
            assert_eq!(
                flag.unwrap().1,
                Type::Bool,
                "flag should be Bool (not Bool?)"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_col_expr_coalesce_strips_nullable() {
    // frame { x: [1.0, None, 3.0] } |> mutate(safe: coalesce(:x, 0.0))
    // x is Float?, coalesce with non-nullable fallback → Float (not Float?)
    let df = frame_literal(vec![(
        "x",
        vec![lit_float(1.0), none_expr(), lit_float(3.0)],
    )]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("safe".into()),
            col_call("coalesce", vec![col_atom("x"), col_lit_float(0.0)]),
        )]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "coalesce should not error: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let safe = row.fields.iter().find(|(l, _)| l.as_str() == "safe");
            assert!(safe.is_some(), "should have 'safe' column");
            assert_eq!(
                safe.unwrap().1,
                Type::Float,
                "coalesce(:x, 0.0) should return Float (nullable stripped)"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_col_expr_coalesce_both_nullable() {
    // frame { x: [1.0, None], y: [None, 2.0] } |> mutate(z: coalesce(:x, :y))
    // Both nullable → result stays nullable (second arg's nullability)
    let df = frame_literal(vec![
        ("x", vec![lit_float(1.0), none_expr()]),
        ("y", vec![none_expr(), lit_float(2.0)]),
    ]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("z".into()),
            col_call("coalesce", vec![col_atom("x"), col_atom("y")]),
        )]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "coalesce both nullable should not error: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let z = row.fields.iter().find(|(l, _)| l.as_str() == "z");
            assert!(z.is_some(), "should have 'z' column");
            assert_eq!(
                z.unwrap().1,
                Type::Option(Box::new(Type::Float)),
                "coalesce of two nullable cols should stay nullable"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_col_expr_is_none_on_nullable() {
    // frame { x: [1, None, 3] } |> mutate(missing: is_none(:x))
    // is_none returns Col(Bool), always non-nullable
    let df = frame_literal(vec![("x", vec![lit_int(1), none_expr(), lit_int(3)])]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("missing".into()),
            col_call("is_none", vec![col_atom("x")]),
        )]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
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
        "is_none should not error: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let missing = row.fields.iter().find(|(l, _)| l.as_str() == "missing");
            assert!(missing.is_some(), "should have 'missing' column");
            assert_eq!(
                missing.unwrap().1,
                Type::Bool,
                "is_none should return Bool (non-nullable)"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_col_expr_none_in_coalesce_ok() {
    // coalesce(:x, None) is NOT banned — only == None / != None is banned
    let df = frame_literal(vec![("x", vec![lit_int(1), none_expr(), lit_int(3)])]);
    let mutate = df_verb(
        DfVerbKind::Mutate,
        DfVerbArgs::Mutate(vec![DfColAssignment::Named(
            sp("z".into()),
            col_call("coalesce", vec![col_atom("x"), col_none()]),
        )]),
    );
    let expr = df_pipe(df, mutate);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    // The None in coalesce is fine — it's function argument, not equality comparison
    assert!(
        !unifier.has_errors(),
        "None as coalesce arg should not be banned: {:?}",
        unifier.errors()
    );
}

#[test]
fn infer_filter_accepts_nullable_bool() {
    // frame { x: [1, None, 3] } |> filter(:x > 2)
    // :x is Int?, so :x > 2 produces Col(Bool?), filter should accept it
    let df = frame_literal(vec![("x", vec![lit_int(1), none_expr(), lit_int(3)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(BinOp::Gt, col_atom("x"), col_lit_int(2))),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
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
        "filter should accept Bool? predicate: {:?}",
        unifier.errors()
    );

    // Schema should be preserved with nullable column
    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let x = row.fields.iter().find(|(l, _)| l.as_str() == "x");
            assert!(x.is_some(), "should have 'x' column");
            assert_eq!(
                x.unwrap().1,
                Type::Option(Box::new(Type::Int)),
                "x should stay Int?"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_capture_nullable_in_comparison() {
    // let threshold: Float? = ...
    // frame { price: [1.0, 2.0] } |> filter(:price > $threshold)
    // $threshold is Float?, so comparison produces Col(Bool?)
    let df = frame_literal(vec![("price", vec![lit_float(1.0), lit_float(2.0)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_binop(
            BinOp::Gt,
            col_atom("price"),
            col_capture("threshold"),
        )),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    env.bind(
        "threshold".into(),
        TypeScheme::mono(Type::Option(Box::new(Type::Float))),
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
        "nullable capture in comparison should work: {:?}",
        unifier.errors()
    );
    assert!(
        matches!(&ty, Type::DataFrame(_)),
        "expected DataFrame, got {:?}",
        ty
    );
}

#[test]
fn infer_sum_always_nullable() {
    // frame { x: [1, 2, 3] } |> group_by(:x) |> summarize(total: sum(:x))
    // x is non-nullable Int, but sum() returns Int? (empty group → null)
    // This is already tested by infer_summarize_sum_returns_column_type,
    // but explicitly verifying with non-nullable input for clarity
    let df = frame_literal(vec![("x", vec![lit_int(1), lit_int(2), lit_int(3)])]);
    let group = df_verb(
        DfVerbKind::GroupBy,
        DfVerbArgs::GroupBy(vec![sp("x".into())]),
    );
    let summarize = df_verb(
        DfVerbKind::Summarize,
        DfVerbArgs::Summarize(vec![DfColAssignment::Named(
            sp("total".into()),
            col_call("sum", vec![col_atom("x")]),
        )]),
    );
    let expr = df_pipe(df_pipe(df, group), summarize);
    let mut env = TypeEnv::new();
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
        "sum should not error: {:?}",
        unifier.errors()
    );

    if let Type::DataFrame(inner) = &ty {
        if let Type::AnonRecord(row) = inner.as_ref() {
            let total = row.fields.iter().find(|(l, _)| l.as_str() == "total");
            assert!(total.is_some(), "should have 'total' column");
            assert_eq!(
                total.unwrap().1,
                Type::Option(Box::new(Type::Int)),
                "sum of non-nullable Int should still return Int? (empty group → null)"
            );
        } else {
            panic!("expected AnonRecord, got {:?}", inner);
        }
    } else {
        panic!("expected DataFrame, got {:?}", ty);
    }
}

#[test]
fn infer_filter_non_bool_clear_error() {
    // filter(:name) where name is String → error about boolean predicate
    let df = frame_literal(vec![("name", vec![lit_str("Alice"), lit_str("Bob")])]);
    let filter = df_verb(DfVerbKind::Filter, DfVerbArgs::Filter(col_atom("name")));
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
    let mut unifier = Unifier::new();
    let _ty = infer_and_resolve(
        &expr,
        &mut env,
        &mut unifier,
        &records,
        &traits,
        &SumTypeRegistry::new(),
    );

    assert!(unifier.has_errors(), "filter(:name) on String should error");
}

#[test]
fn infer_col_expr_impure_function_reports_purity_violation() {
    let df = frame_literal(vec![("x", vec![lit_int(1)])]);
    let filter = df_verb(
        DfVerbKind::Filter,
        DfVerbArgs::Filter(col_call("io_fn", vec![col_atom("x")])),
    );
    let expr = df_pipe(df, filter);
    let mut env = TypeEnv::new();
    env.set_function_effect("io_fn".to_string(), Effects::impure());
    let records = RecordRegistry::new();
    let traits = TraitRegistry::new();
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
        "impure function in col expr should error"
    );
    assert!(
        unifier
            .errors()
            .iter()
            .any(|d| d.category == Category::PurityViolation),
        "expected PurityViolation diagnostic, got {:?}",
        unifier.errors()
    );
}

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
        }),
    );
    // fn get(self) -> Int
    methods.insert(
        "get".to_string(),
        Type::Function(FunctionType {
            params: vec![counter.clone()],
            ret: Box::new(Type::Int),
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
        }),
    );
    // get(self) -> Int  (CallPure — returns non-Self)
    methods.insert(
        "get".to_string(),
        Type::Function(FunctionType {
            params: vec![counter_ty.clone()],
            ret: Box::new(Type::Int),
        }),
    );
    // get_and_update(self, Int) -> #(Counter, Int)  (CallWithState)
    methods.insert(
        "get_and_update".to_string(),
        Type::Function(FunctionType {
            params: vec![counter_ty.clone(), Type::Int],
            ret: Box::new(Type::Tuple(vec![counter_ty.clone(), Type::Int])),
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
