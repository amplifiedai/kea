//! Typed high-level IR (HIR) for Kea.
//!
//! HIR is the typed/desugared boundary between frontend inference and backend lowering.
//! This initial slice provides a stable typed representation for function declarations
//! and expression trees, with a conservative fallback for unsupported syntax.

use std::collections::{BTreeMap, BTreeSet};

use kea_ast::{
    BinOp, CaseArm, DeclKind, Expr, ExprDecl, ExprKind, FnDecl, Lit, Module, Param, Pattern,
    PatternKind, Span, TypeAnnotation, UnaryOp,
};
use kea_infer::typeck::TypeEnv;
use kea_types::{EffectRow, FunctionType, Type};

#[derive(Debug, Clone, PartialEq)]
pub struct HirModule {
    pub declarations: Vec<HirDecl>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum HirDecl {
    Function(HirFunction),
    Raw(DeclKind),
}

#[derive(Debug, Clone, PartialEq)]
pub struct HirFunction {
    pub name: String,
    pub params: Vec<HirParam>,
    pub body: HirExpr,
    pub ty: Type,
    pub effects: EffectRow,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HirParam {
    pub name: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HirExpr {
    pub kind: HirExprKind,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum HirExprKind {
    Lit(Lit),
    Var(String),
    RecordLit {
        record_type: String,
        fields: Vec<(String, HirExpr)>,
    },
    SumConstructor {
        sum_type: String,
        variant: String,
        tag: i64,
        fields: Vec<HirExpr>,
    },
    SumPayloadAccess {
        expr: Box<HirExpr>,
        sum_type: String,
        variant: String,
        field_index: usize,
    },
    FieldAccess {
        expr: Box<HirExpr>,
        field: String,
    },
    Binary {
        op: BinOp,
        left: Box<HirExpr>,
        right: Box<HirExpr>,
    },
    Unary {
        op: UnaryOp,
        operand: Box<HirExpr>,
    },
    Call {
        func: Box<HirExpr>,
        args: Vec<HirExpr>,
    },
    Lambda {
        params: Vec<HirParam>,
        body: Box<HirExpr>,
    },
    Let {
        pattern: HirPattern,
        value: Box<HirExpr>,
    },
    If {
        condition: Box<HirExpr>,
        then_branch: Box<HirExpr>,
        else_branch: Option<Box<HirExpr>>,
    },
    Block(Vec<HirExpr>),
    Tuple(Vec<HirExpr>),
    Raw(ExprKind),
}

#[derive(Debug, Clone, PartialEq)]
pub enum HirPattern {
    Var(String),
    Raw(PatternKind),
}

type UnitVariantTags = BTreeMap<String, i64>;
type QualifiedUnitVariantTags = BTreeMap<(String, String), i64>;
#[derive(Debug, Clone, PartialEq, Eq)]
struct PatternVariantMeta {
    tag: i64,
    sum_type: String,
    arity: usize,
    field_types: Vec<Type>,
}
type PatternVariantTags = BTreeMap<String, PatternVariantMeta>;
type QualifiedPatternVariantTags = BTreeMap<(String, String), PatternVariantMeta>;
type KnownRecordDefs = BTreeSet<String>;

fn is_namespace_qualifier(name: &str) -> bool {
    name.chars().next().is_some_and(|ch| ch.is_ascii_uppercase())
}

fn expr_decl_to_fn_decl(expr: &ExprDecl) -> FnDecl {
    FnDecl {
        public: expr.public,
        name: expr.name.clone(),
        doc: expr.doc.clone(),
        annotations: expr.annotations.clone(),
        params: expr.params.clone(),
        return_annotation: expr.return_annotation.clone(),
        effect_annotation: expr.effect_annotation.clone(),
        body: expr.body.clone(),
        testing: expr.testing.clone(),
        testing_tags: expr.testing_tags.clone(),
        span: expr.span,
        where_clause: expr.where_clause.clone(),
    }
}

fn lower_pattern_type_annotation(annotation: &TypeAnnotation) -> Type {
    match annotation {
        TypeAnnotation::Named(name) => match name.as_str() {
            "Int" => Type::Int,
            "Float" => Type::Float,
            "Bool" => Type::Bool,
            "String" => Type::String,
            "Unit" => Type::Unit,
            _ => Type::Dynamic,
        },
        _ => Type::Dynamic,
    }
}

fn collect_variant_tags(
    module: &Module,
) -> (
    UnitVariantTags,
    QualifiedUnitVariantTags,
    PatternVariantTags,
    QualifiedPatternVariantTags,
) {
    let mut unqualified = UnitVariantTags::new();
    let mut qualified = QualifiedUnitVariantTags::new();
    let mut duplicates = BTreeSet::new();
    let mut pattern_unqualified = PatternVariantTags::new();
    let mut pattern_qualified = QualifiedPatternVariantTags::new();
    let mut pattern_duplicates = BTreeSet::new();

    for decl in &module.declarations {
        let DeclKind::TypeDef(def) = &decl.node else {
            continue;
        };

        for (idx, variant) in def.variants.iter().enumerate() {
            let tag = idx as i64;
            let meta = PatternVariantMeta {
                tag,
                sum_type: def.name.node.clone(),
                arity: variant.fields.len(),
                field_types: variant
                    .fields
                    .iter()
                    .map(|field| lower_pattern_type_annotation(&field.ty.node))
                    .collect(),
            };
            pattern_qualified.insert(
                (def.name.node.clone(), variant.name.node.clone()),
                meta.clone(),
            );
            if pattern_unqualified
                .insert(variant.name.node.clone(), meta)
                .is_some()
            {
                pattern_duplicates.insert(variant.name.node.clone());
            }

            if !variant.fields.is_empty() {
                continue;
            }

            qualified.insert((def.name.node.clone(), variant.name.node.clone()), tag);

            if unqualified
                .insert(variant.name.node.clone(), tag)
                .is_some()
            {
                duplicates.insert(variant.name.node.clone());
            }
        }
    }

    for name in duplicates {
        unqualified.remove(&name);
    }
    for name in pattern_duplicates {
        pattern_unqualified.remove(&name);
    }

    (unqualified, qualified, pattern_unqualified, pattern_qualified)
}

fn collect_record_defs(module: &Module) -> KnownRecordDefs {
    module
        .declarations
        .iter()
        .filter_map(|decl| match &decl.node {
            DeclKind::RecordDef(def) => Some(def.name.node.clone()),
            _ => None,
        })
        .collect()
}

fn resolve_unqualified_constructor_meta(
    name: &str,
    arity: usize,
    pattern_variant_tags: &PatternVariantTags,
) -> Option<PatternVariantMeta> {
    pattern_variant_tags
        .get(name)
        .filter(|meta| meta.arity == arity)
        .cloned()
}

pub fn lower_module(module: &Module, env: &TypeEnv) -> HirModule {
    let (unit_variant_tags, qualified_variant_tags, pattern_variant_tags, pattern_qualified_tags) =
        collect_variant_tags(module);
    let known_record_defs = collect_record_defs(module);
    let declarations = module
        .declarations
        .iter()
        .map(|decl| match &decl.node {
            DeclKind::Function(fn_decl) => HirDecl::Function(lower_function_with_variants(
                fn_decl,
                env,
                &unit_variant_tags,
                &qualified_variant_tags,
                &pattern_variant_tags,
                &pattern_qualified_tags,
                &known_record_defs,
            )),
            DeclKind::ExprFn(expr_decl) => HirDecl::Function(lower_function_with_variants(
                &expr_decl_to_fn_decl(expr_decl),
                env,
                &unit_variant_tags,
                &qualified_variant_tags,
                &pattern_variant_tags,
                &pattern_qualified_tags,
                &known_record_defs,
            )),
            other => HirDecl::Raw(other.clone()),
        })
        .collect();
    HirModule { declarations }
}

pub fn lower_function(fn_decl: &FnDecl, env: &TypeEnv) -> HirFunction {
    let known_record_defs = BTreeSet::new();
    lower_function_with_variants(
        fn_decl,
        env,
        &UnitVariantTags::new(),
        &QualifiedUnitVariantTags::new(),
        &PatternVariantTags::new(),
        &QualifiedPatternVariantTags::new(),
        &known_record_defs,
    )
}

fn lower_function_with_variants(
    fn_decl: &FnDecl,
    env: &TypeEnv,
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
    pattern_variant_tags: &PatternVariantTags,
    pattern_qualified_tags: &QualifiedPatternVariantTags,
    known_record_defs: &KnownRecordDefs,
) -> HirFunction {
    let fn_ty = env
        .lookup(&fn_decl.name.node)
        .map(|scheme| scheme.ty.clone())
        .unwrap_or_else(|| Type::Function(FunctionType::pure(vec![], Type::Dynamic)));

    let (effects, ret_ty) = match &fn_ty {
        Type::Function(ft) => (ft.effects.clone(), ft.ret.as_ref().clone()),
        _ => (EffectRow::pure(), Type::Dynamic),
    };

    HirFunction {
        name: fn_decl.name.node.clone(),
        params: fn_decl.params.iter().map(lower_param).collect(),
        body: lower_expr(
            &fn_decl.body,
            Some(ret_ty),
            unit_variant_tags,
            qualified_variant_tags,
            pattern_variant_tags,
            pattern_qualified_tags,
            known_record_defs,
        ),
        ty: fn_ty,
        effects,
        span: fn_decl.span,
    }
}

fn lower_param(param: &Param) -> HirParam {
    HirParam {
        name: param.name().map(ToOwned::to_owned),
        span: param.span(),
    }
}

fn lower_pattern(pattern: &Pattern) -> HirPattern {
    match &pattern.node {
        PatternKind::Var(name) => HirPattern::Var(name.clone()),
        other => HirPattern::Raw(other.clone()),
    }
}

fn lower_expr(
    expr: &Expr,
    ty_hint: Option<Type>,
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
    pattern_variant_tags: &PatternVariantTags,
    pattern_qualified_tags: &QualifiedPatternVariantTags,
    known_record_defs: &KnownRecordDefs,
) -> HirExpr {
    let default_ty = ty_hint.clone().unwrap_or(Type::Dynamic);

    let kind = match &expr.node {
        ExprKind::Lit(lit) => HirExprKind::Lit(lit.clone()),
        ExprKind::Var(name) => HirExprKind::Var(name.clone()),
        ExprKind::BinaryOp { op, left, right } => HirExprKind::Binary {
            op: op.node,
            left: Box::new(lower_expr(
                left,
                None,
                unit_variant_tags,
                qualified_variant_tags,
                pattern_variant_tags,
                pattern_qualified_tags,
                known_record_defs,
            )),
            right: Box::new(lower_expr(
                right,
                None,
                unit_variant_tags,
                qualified_variant_tags,
                pattern_variant_tags,
                pattern_qualified_tags,
                known_record_defs,
            )),
        },
        ExprKind::UnaryOp { op, operand } => HirExprKind::Unary {
            op: op.node,
            operand: Box::new(lower_expr(
                operand,
                None,
                unit_variant_tags,
                qualified_variant_tags,
                pattern_variant_tags,
                pattern_qualified_tags,
                known_record_defs,
            )),
        },
        ExprKind::Call { func, args } => HirExprKind::Call {
            func: Box::new(lower_expr(
                func,
                None,
                unit_variant_tags,
                qualified_variant_tags,
                pattern_variant_tags,
                pattern_qualified_tags,
                known_record_defs,
            )),
            args: args
                .iter()
                .map(|arg| {
                    lower_expr(
                        &arg.value,
                        None,
                        unit_variant_tags,
                        qualified_variant_tags,
                        pattern_variant_tags,
                        pattern_qualified_tags,
                        known_record_defs,
                    )
                })
                .collect(),
        },
        ExprKind::Lambda { params, body, .. } => HirExprKind::Lambda {
            params: params.iter().map(lower_param).collect(),
            body: Box::new(lower_expr(
                body,
                None,
                unit_variant_tags,
                qualified_variant_tags,
                pattern_variant_tags,
                pattern_qualified_tags,
                known_record_defs,
            )),
        },
        ExprKind::Let { pattern, value, .. } => HirExprKind::Let {
            pattern: lower_pattern(pattern),
            value: Box::new(lower_expr(
                value,
                None,
                unit_variant_tags,
                qualified_variant_tags,
                pattern_variant_tags,
                pattern_qualified_tags,
                known_record_defs,
            )),
        },
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => HirExprKind::If {
            condition: Box::new(lower_expr(
                condition,
                None,
                unit_variant_tags,
                qualified_variant_tags,
                pattern_variant_tags,
                pattern_qualified_tags,
                known_record_defs,
            )),
            then_branch: Box::new(lower_expr(
                then_branch,
                ty_hint.clone(),
                unit_variant_tags,
                qualified_variant_tags,
                pattern_variant_tags,
                pattern_qualified_tags,
                known_record_defs,
            )),
            else_branch: else_branch
                .as_ref()
                .map(|expr| {
                    Box::new(lower_expr(
                        expr,
                        ty_hint.clone(),
                        unit_variant_tags,
                        qualified_variant_tags,
                        pattern_variant_tags,
                        pattern_qualified_tags,
                        known_record_defs,
                    ))
                }),
        },
        ExprKind::Case { scrutinee, arms } => {
            if let Some(case_kind) = lower_bool_case(
                scrutinee,
                arms,
                ty_hint.clone(),
                unit_variant_tags,
                qualified_variant_tags,
                pattern_variant_tags,
                pattern_qualified_tags,
                known_record_defs,
            ) {
                case_kind
            } else {
                HirExprKind::Raw(expr.node.clone())
            }
        }
        ExprKind::Block(exprs) => {
            let last_idx = exprs.len().saturating_sub(1);
            HirExprKind::Block(
                exprs
                    .iter()
                    .enumerate()
                    .map(|(idx, inner)| {
                        let hint = if idx == last_idx { ty_hint.clone() } else { None };
                        lower_expr(
                            inner,
                            hint,
                            unit_variant_tags,
                            qualified_variant_tags,
                            pattern_variant_tags,
                            pattern_qualified_tags,
                            known_record_defs,
                        )
                    })
                    .collect(),
            )
        }
        ExprKind::Tuple(exprs) => HirExprKind::Tuple(
            exprs
                .iter()
                .map(|inner| {
                    lower_expr(
                        inner,
                        None,
                        unit_variant_tags,
                        qualified_variant_tags,
                        pattern_variant_tags,
                        pattern_qualified_tags,
                        known_record_defs,
                    )
                })
                .collect(),
        ),
        ExprKind::Record {
            name,
            fields,
            spread,
        } if spread.is_none() && known_record_defs.contains(&name.node) => HirExprKind::RecordLit {
            record_type: name.node.clone(),
            fields: fields
                .iter()
                .map(|(field_name, field_value)| {
                    (
                        field_name.node.clone(),
                        lower_expr(
                            field_value,
                            None,
                            unit_variant_tags,
                            qualified_variant_tags,
                            pattern_variant_tags,
                            pattern_qualified_tags,
                            known_record_defs,
                        ),
                    )
                })
                .collect(),
        },
        ExprKind::Constructor { name, args } => {
            if args.is_empty() {
                if let Some(tag) = unit_variant_tags.get(&name.node) {
                    HirExprKind::Lit(Lit::Int(*tag))
                } else {
                    HirExprKind::Raw(expr.node.clone())
                }
            } else if let Some(meta) =
                resolve_unqualified_constructor_meta(&name.node, args.len(), pattern_variant_tags)
            {
                HirExprKind::SumConstructor {
                    sum_type: meta.sum_type,
                    variant: name.node.clone(),
                    tag: meta.tag,
                    fields: args
                        .iter()
                        .map(|arg| {
                            lower_expr(
                                &arg.value,
                                None,
                                unit_variant_tags,
                                qualified_variant_tags,
                                pattern_variant_tags,
                                pattern_qualified_tags,
                                known_record_defs,
                            )
                        })
                        .collect(),
                }
            } else {
                HirExprKind::Raw(expr.node.clone())
            }
        }
        ExprKind::FieldAccess { expr: qualifier, field } => {
            if let ExprKind::Var(type_name) = &qualifier.node {
                if let Some(tag) = qualified_variant_tags.get(&(type_name.clone(), field.node.clone()))
                {
                    HirExprKind::Lit(Lit::Int(*tag))
                } else if is_namespace_qualifier(type_name) {
                    HirExprKind::Var(format!("{type_name}::{}", field.node))
                } else {
                    HirExprKind::FieldAccess {
                        expr: Box::new(lower_expr(
                            qualifier,
                            None,
                            unit_variant_tags,
                            qualified_variant_tags,
                            pattern_variant_tags,
                            pattern_qualified_tags,
                            known_record_defs,
                        )),
                        field: field.node.clone(),
                    }
                }
            } else {
                HirExprKind::FieldAccess {
                    expr: Box::new(lower_expr(
                        qualifier,
                        None,
                        unit_variant_tags,
                        qualified_variant_tags,
                        pattern_variant_tags,
                        pattern_qualified_tags,
                        known_record_defs,
                    )),
                    field: field.node.clone(),
                }
            }
        }
        other => HirExprKind::Raw(other.clone()),
    };

    let ty = match &expr.node {
        ExprKind::Lit(Lit::Int(_)) => Type::Int,
        ExprKind::Lit(Lit::Float(_)) => Type::Float,
        ExprKind::Lit(Lit::Bool(_)) => Type::Bool,
        ExprKind::Lit(Lit::String(_)) => Type::String,
        ExprKind::Lit(Lit::Unit) => Type::Unit,
        ExprKind::BinaryOp { op, left, .. } => match op.node {
            BinOp::Eq
            | BinOp::Neq
            | BinOp::Lt
            | BinOp::Lte
            | BinOp::Gt
            | BinOp::Gte
            | BinOp::And
            | BinOp::Or
            | BinOp::In
            | BinOp::NotIn => Type::Bool,
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::Concat
            | BinOp::Combine => match &left.node {
                ExprKind::Lit(Lit::Int(_)) => Type::Int,
                ExprKind::Lit(Lit::Float(_)) => Type::Float,
                ExprKind::Lit(Lit::String(_)) => Type::String,
                _ => default_ty,
            },
        },
        ExprKind::UnaryOp { op, operand } => match op.node {
            UnaryOp::Neg => match &operand.node {
                ExprKind::Lit(Lit::Int(_)) => Type::Int,
                ExprKind::Lit(Lit::Float(_)) => Type::Float,
                _ => default_ty,
            },
            UnaryOp::Not => Type::Bool,
        },
        ExprKind::Constructor { name, args } => {
            if args.is_empty() && unit_variant_tags.contains_key(&name.node) {
                Type::Int
            } else if default_ty != Type::Dynamic {
                default_ty
            } else if let Some(meta) =
                resolve_unqualified_constructor_meta(&name.node, args.len(), pattern_variant_tags)
            {
                Type::Sum(kea_types::SumType {
                    name: meta.sum_type,
                    type_args: vec![],
                    variants: vec![(name.node.clone(), meta.field_types)],
                })
            } else {
                default_ty
            }
        }
        ExprKind::FieldAccess { expr: qualifier, field } => {
            if let ExprKind::Var(type_name) = &qualifier.node {
                if qualified_variant_tags.contains_key(&(type_name.clone(), field.node.clone())) {
                    Type::Int
                } else {
                    default_ty
                }
            } else {
                default_ty
            }
        }
        ExprKind::Record { name, spread, .. }
            if spread.is_none() && known_record_defs.contains(&name.node) =>
        {
            Type::Record(kea_types::RecordType {
                name: name.node.clone(),
                params: vec![],
                row: kea_types::RowType::empty_closed(),
            })
        }
        _ => default_ty,
    };

    HirExpr {
        kind,
        ty,
        span: expr.span,
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum LiteralCaseValue {
    Int(i64),
    Float(f64),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ConstructorPayloadBind {
    name: String,
    sum_type: String,
    variant: String,
    field_index: usize,
    field_ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
struct ConstructorPayloadCheck {
    sum_type: String,
    variant: String,
    field_index: usize,
    field_ty: Type,
    expected: LiteralCaseValue,
}

type LiteralArm<'a> = (
    LiteralCaseValue,
    &'a Expr,
    Option<String>,
    Vec<ConstructorPayloadBind>,
    Vec<ConstructorPayloadCheck>,
    Option<&'a Expr>,
);

type LiteralCasePatternInfo = (
    Vec<LiteralCaseValue>,
    Option<String>,
    Vec<ConstructorPayloadBind>,
    Vec<ConstructorPayloadCheck>,
);

#[allow(clippy::too_many_arguments)]
fn lower_bool_case(
    scrutinee: &Expr,
    arms: &[CaseArm],
    ty_hint: Option<Type>,
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
    pattern_variant_tags: &PatternVariantTags,
    pattern_qualified_tags: &QualifiedPatternVariantTags,
    known_record_defs: &KnownRecordDefs,
) -> Option<HirExprKind> {
    if let Some(kind) = lower_literal_case(
        scrutinee,
        arms,
        ty_hint.clone(),
        unit_variant_tags,
        qualified_variant_tags,
        pattern_variant_tags,
        pattern_qualified_tags,
        known_record_defs,
    ) {
        return Some(kind);
    }

    if arms.iter().any(|arm| arm.guard.is_some()) {
        return None;
    }

    let return_ty = ty_hint.clone().unwrap_or(Type::Dynamic);
    let lowered_scrutinee = lower_expr(
        scrutinee,
        None,
        unit_variant_tags,
        qualified_variant_tags,
        pattern_variant_tags,
        pattern_qualified_tags,
        known_record_defs,
    );
    let safe_scrutinee = matches!(lowered_scrutinee.kind, HirExprKind::Var(_) | HirExprKind::Lit(_));
    let (scrutinee_expr, setup_expr) = if safe_scrutinee {
        (lowered_scrutinee.clone(), None)
    } else {
        let temp_name = format!(
            "__kea_case_scrutinee${}_{}",
            scrutinee.span.start, scrutinee.span.end
        );
        let temp_var = HirExpr {
            kind: HirExprKind::Var(temp_name.clone()),
            ty: lowered_scrutinee.ty.clone(),
            span: scrutinee.span,
        };
        let setup = HirExpr {
            kind: HirExprKind::Let {
                pattern: HirPattern::Var(temp_name),
                value: Box::new(lowered_scrutinee),
            },
            ty: temp_var.ty.clone(),
            span: scrutinee.span,
        };
        (temp_var, Some(setup))
    };

    let lower_branch_with_bind = |body: &Expr, bind: Option<String>| {
        let lowered_body = lower_expr(
            body,
            ty_hint.clone(),
            unit_variant_tags,
            qualified_variant_tags,
            pattern_variant_tags,
            pattern_qualified_tags,
            known_record_defs,
        );
        match bind {
            Some(name) => HirExpr {
                kind: HirExprKind::Block(vec![
                    HirExpr {
                        kind: HirExprKind::Let {
                            pattern: HirPattern::Var(name),
                            value: Box::new(scrutinee_expr.clone()),
                        },
                        ty: scrutinee_expr.ty.clone(),
                        span: scrutinee.span,
                    },
                    lowered_body.clone(),
                ]),
                ty: lowered_body.ty,
                span: lowered_body.span,
            },
            None => lowered_body,
        }
    };

    if arms.len() == 1 {
        let lowered = match &arms[0].pattern.node {
            PatternKind::Wildcard => lower_branch_with_bind(&arms[0].body, None),
            PatternKind::Var(name) => lower_branch_with_bind(&arms[0].body, Some(name.clone())),
            _ => return None,
        };
        if let Some(setup) = setup_expr {
            return Some(HirExprKind::Block(vec![setup, lowered]));
        }
        return Some(lowered.kind);
    }

    let mut true_body: Option<&Expr> = None;
    let mut false_body: Option<&Expr> = None;
    let mut wildcard_body: Option<&Expr> = None;
    let mut var_body: Option<(&Expr, String)> = None;

    for arm in arms {
        match &arm.pattern.node {
            PatternKind::Lit(Lit::Bool(true)) => true_body = Some(&arm.body),
            PatternKind::Lit(Lit::Bool(false)) => false_body = Some(&arm.body),
            PatternKind::Wildcard => wildcard_body = Some(&arm.body),
            PatternKind::Var(name) => var_body = Some((&arm.body, name.clone())),
            _ => return None,
        }
    }

    let lowered_if = match (true_body, false_body, wildcard_body, var_body) {
        (Some(then_body), Some(else_body), None, None) if arms.len() == 2 => {
            Some(HirExprKind::If {
                condition: Box::new(scrutinee_expr.clone()),
                then_branch: Box::new(lower_branch_with_bind(then_body, None)),
                else_branch: Some(Box::new(lower_branch_with_bind(else_body, None))),
            })
        }
        (Some(then_body), None, Some(default_body), None) if arms.len() == 2 => {
            Some(HirExprKind::If {
                condition: Box::new(scrutinee_expr.clone()),
                then_branch: Box::new(lower_branch_with_bind(then_body, None)),
                else_branch: Some(Box::new(lower_branch_with_bind(default_body, None))),
            })
        }
        (None, Some(else_body), Some(default_body), None) if arms.len() == 2 => {
            Some(HirExprKind::If {
                condition: Box::new(scrutinee_expr.clone()),
                then_branch: Box::new(lower_branch_with_bind(default_body, None)),
                else_branch: Some(Box::new(lower_branch_with_bind(else_body, None))),
            })
        }
        (Some(then_body), None, None, Some((default_body, bind_name))) if arms.len() == 2 => {
            Some(HirExprKind::If {
                condition: Box::new(scrutinee_expr.clone()),
                then_branch: Box::new(lower_branch_with_bind(then_body, None)),
                else_branch: Some(Box::new(lower_branch_with_bind(
                    default_body,
                    Some(bind_name),
                ))),
            })
        }
        (None, Some(else_body), None, Some((default_body, bind_name))) if arms.len() == 2 => {
            Some(HirExprKind::If {
                condition: Box::new(scrutinee_expr.clone()),
                then_branch: Box::new(lower_branch_with_bind(
                    default_body,
                    Some(bind_name),
                )),
                else_branch: Some(Box::new(lower_branch_with_bind(else_body, None))),
            })
        }
        _ => None,
    }?;

    if let Some(setup) = setup_expr {
        Some(HirExprKind::Block(vec![
            setup,
            HirExpr {
                kind: lowered_if,
                ty: return_ty,
                span: scrutinee.span,
            },
        ]))
    } else {
        Some(lowered_if)
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_literal_case(
    scrutinee: &Expr,
    arms: &[CaseArm],
    ty_hint: Option<Type>,
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
    pattern_variant_tags: &PatternVariantTags,
    pattern_qualified_tags: &QualifiedPatternVariantTags,
    known_record_defs: &KnownRecordDefs,
) -> Option<HirExprKind> {
    enum LiteralFallbackArm<'a> {
        Wild {
            body: &'a Expr,
            guard: Option<&'a Expr>,
        },
        Var {
            name: String,
            body: &'a Expr,
            guard: Option<&'a Expr>,
        },
    }

    let mut literal_arms: Vec<LiteralArm<'_>> = Vec::new();
    let mut fallback_arms: Vec<LiteralFallbackArm<'_>> = Vec::new();
    for arm in arms {
        match &arm.pattern.node {
            PatternKind::Wildcard => fallback_arms.push(LiteralFallbackArm::Wild {
                body: &arm.body,
                guard: arm.guard.as_deref(),
            }),
            PatternKind::Var(name) => fallback_arms.push(LiteralFallbackArm::Var {
                name: name.clone(),
                body: &arm.body,
                guard: arm.guard.as_deref(),
            }),
            pattern => {
                let (values, bind_name, payload_binds, payload_checks) =
                    literal_case_values_from_pattern(
                    pattern,
                    pattern_variant_tags,
                    pattern_qualified_tags,
                )?;
                for value in values {
                    literal_arms.push((
                        value,
                        &arm.body,
                        bind_name.clone(),
                        payload_binds.clone(),
                        payload_checks.clone(),
                        arm.guard.as_deref(),
                    ));
                }
            }
        }
    }

    let has_true = literal_arms
        .iter()
        .any(|(lit, _, _, _, _, _)| matches!(lit, LiteralCaseValue::Bool(true)));
    let has_false = literal_arms
        .iter()
        .any(|(lit, _, _, _, _, _)| matches!(lit, LiteralCaseValue::Bool(false)));
    if fallback_arms.is_empty()
        && (has_true || has_false)
        && arms.iter().all(|arm| arm.guard.is_none())
        && arms
            .iter()
            .all(|arm| bool_case_fallback_compatible(&arm.pattern.node))
    {
        // Let the dedicated bool-case lowering path handle exhaustive bool cases
        // without introducing synthetic non-exhaustive branches.
        return None;
    }

    // Non-exhaustive literal chains without a fallback would introduce
    // missing-value paths for non-Unit expressions.
    let return_ty = ty_hint.clone().unwrap_or(Type::Dynamic);

    let lowered_scrutinee = lower_expr(
        scrutinee,
        None,
        unit_variant_tags,
        qualified_variant_tags,
        pattern_variant_tags,
        pattern_qualified_tags,
        known_record_defs,
    );
    let safe_scrutinee = matches!(lowered_scrutinee.kind, HirExprKind::Var(_) | HirExprKind::Lit(_));
    let (scrutinee_expr, setup_expr) = if safe_scrutinee {
        (lowered_scrutinee.clone(), None)
    } else {
        // Avoid re-evaluating arbitrary scrutinee expressions in each arm condition.
        let temp_name = format!(
            "__kea_case_scrutinee${}_{}",
            scrutinee.span.start, scrutinee.span.end
        );
        let temp_var = HirExpr {
            kind: HirExprKind::Var(temp_name.clone()),
            ty: lowered_scrutinee.ty.clone(),
            span: scrutinee.span,
        };
        let setup = HirExpr {
            kind: HirExprKind::Let {
                pattern: HirPattern::Var(temp_name),
                value: Box::new(lowered_scrutinee),
            },
            ty: temp_var.ty.clone(),
            span: scrutinee.span,
        };
        (temp_var, Some(setup))
    };

    let unit_else = HirExpr {
        kind: HirExprKind::Lit(Lit::Unit),
        ty: Type::Unit,
        span: scrutinee.span,
    };
    let mut else_expr: Option<HirExpr> = None;
    for fallback in fallback_arms.into_iter().rev() {
        match fallback {
            LiteralFallbackArm::Wild { body, guard } => {
                let then_branch = lower_expr(
                    body,
                    ty_hint.clone(),
                    unit_variant_tags,
                    qualified_variant_tags,
                    pattern_variant_tags,
                    pattern_qualified_tags,
                    known_record_defs,
                );
                let Some(guard_expr) = guard else {
                    // Unconditional fallback shadows any later fallback arm.
                    else_expr = Some(then_branch);
                    continue;
                };
                let condition = lower_expr(
                    guard_expr,
                    None,
                    unit_variant_tags,
                    qualified_variant_tags,
                    pattern_variant_tags,
                    pattern_qualified_tags,
                    known_record_defs,
                );
                let next_else = else_expr.clone().or_else(|| {
                    if return_ty == Type::Unit {
                        Some(unit_else.clone())
                    } else {
                        None
                    }
                })?;
                else_expr = Some(HirExpr {
                    kind: HirExprKind::If {
                        condition: Box::new(condition),
                        then_branch: Box::new(then_branch),
                        else_branch: Some(Box::new(next_else)),
                    },
                    ty: return_ty.clone(),
                    span: scrutinee.span,
                });
            }
            LiteralFallbackArm::Var { name, body, guard } => {
                let bind_expr = HirExpr {
                    kind: HirExprKind::Let {
                        pattern: HirPattern::Var(name.clone()),
                        value: Box::new(scrutinee_expr.clone()),
                    },
                    ty: scrutinee_expr.ty.clone(),
                    span: scrutinee.span,
                };
                let then_branch = HirExpr {
                    kind: HirExprKind::Block(vec![
                        bind_expr.clone(),
                        lower_expr(
                            body,
                            ty_hint.clone(),
                            unit_variant_tags,
                            qualified_variant_tags,
                            pattern_variant_tags,
                            pattern_qualified_tags,
                            known_record_defs,
                        ),
                    ]),
                    ty: return_ty.clone(),
                    span: scrutinee.span,
                };
                let Some(guard_expr) = guard else {
                    // Unconditional fallback shadows any later fallback arm.
                    else_expr = Some(then_branch);
                    continue;
                };
                let condition = HirExpr {
                    kind: HirExprKind::Block(vec![
                        bind_expr,
                        lower_expr(
                            guard_expr,
                            None,
                            unit_variant_tags,
                            qualified_variant_tags,
                            pattern_variant_tags,
                            pattern_qualified_tags,
                            known_record_defs,
                        ),
                    ]),
                    ty: Type::Bool,
                    span: scrutinee.span,
                };
                let next_else = else_expr.clone().or_else(|| {
                    if return_ty == Type::Unit {
                        Some(unit_else.clone())
                    } else {
                        None
                    }
                })?;
                else_expr = Some(HirExpr {
                    kind: HirExprKind::If {
                        condition: Box::new(condition),
                        then_branch: Box::new(then_branch),
                        else_branch: Some(Box::new(next_else)),
                    },
                    ty: return_ty.clone(),
                    span: scrutinee.span,
                });
            }
        }
    }

    if else_expr.is_none() && !literal_arms.is_empty() {
        // Type checking enforces exhaustiveness before lowering. For exhaustive literal
        // chains without an explicit fallback (for example unit-enum constructor cases),
        // provide a defensive synthetic else so non-unit MIR value paths stay closed.
        let (_, fallback_body, _, _, _, _) = literal_arms
            .last()
            .expect("checked literal_arms is non-empty");
        else_expr = Some(lower_expr(
            fallback_body,
            ty_hint.clone(),
            unit_variant_tags,
            qualified_variant_tags,
            pattern_variant_tags,
            pattern_qualified_tags,
            known_record_defs,
        ));
    }

    if literal_arms.is_empty() {
        let lowered = else_expr?;
        if let Some(setup) = setup_expr {
            return Some(HirExprKind::Block(vec![setup, lowered]));
        }
        return Some(lowered.kind);
    }

    for (lit, body, bind_name, payload_binds, payload_checks, guard) in
        literal_arms.into_iter().rev()
    {
        let mut condition = HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::Eq,
                left: Box::new(scrutinee_expr.clone()),
                right: Box::new(HirExpr {
                    kind: HirExprKind::Lit(literal_case_lit(lit)),
                    ty: literal_case_type(lit),
                    span: scrutinee.span,
                }),
            },
            ty: Type::Bool,
            span: scrutinee.span,
        };
        for payload_check in payload_checks {
            let payload_expr = HirExpr {
                kind: HirExprKind::SumPayloadAccess {
                    expr: Box::new(scrutinee_expr.clone()),
                    sum_type: payload_check.sum_type,
                    variant: payload_check.variant,
                    field_index: payload_check.field_index,
                },
                ty: payload_check.field_ty,
                span: scrutinee.span,
            };
            let payload_eq = HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::Eq,
                    left: Box::new(payload_expr),
                    right: Box::new(HirExpr {
                        kind: HirExprKind::Lit(literal_case_lit(payload_check.expected)),
                        ty: literal_case_type(payload_check.expected),
                        span: scrutinee.span,
                    }),
                },
                ty: Type::Bool,
                span: scrutinee.span,
            };
            condition = HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::And,
                    left: Box::new(condition),
                    right: Box::new(payload_eq),
                },
                ty: Type::Bool,
                span: scrutinee.span,
            };
        }
        if let Some(guard_expr) = guard {
            let guard_expr = lower_expr(
                guard_expr,
                None,
                unit_variant_tags,
                qualified_variant_tags,
                pattern_variant_tags,
                pattern_qualified_tags,
                known_record_defs,
            );
            let mut binds = build_literal_arm_bindings(
                bind_name.as_deref(),
                &payload_binds,
                &scrutinee_expr,
            );
            let lowered_guard = if binds.is_empty() {
                guard_expr
            } else {
                binds.push(guard_expr);
                HirExpr {
                    kind: HirExprKind::Block(binds),
                    ty: Type::Bool,
                    span: scrutinee.span,
                }
            };
            condition = HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::And,
                    left: Box::new(condition),
                    right: Box::new(lowered_guard),
                },
                ty: Type::Bool,
                span: scrutinee.span,
            };
        }

        let next = HirExpr {
            kind: HirExprKind::If {
                condition: Box::new(condition),
                then_branch: Box::new(lower_arm_body(
                    body,
                    bind_name,
                    payload_binds,
                    &scrutinee_expr,
                    ty_hint.clone(),
                    unit_variant_tags,
                    qualified_variant_tags,
                    pattern_variant_tags,
                    pattern_qualified_tags,
                    known_record_defs,
                )),
                else_branch: else_expr.as_ref().map(|expr| Box::new(expr.clone())),
            },
            ty: return_ty.clone(),
            span: scrutinee.span,
        };
        else_expr = Some(next);
    }

    let lowered = else_expr?;
    if let Some(setup) = setup_expr {
        Some(HirExprKind::Block(vec![setup, lowered]))
    } else {
        Some(lowered.kind)
    }
}

fn literal_case_values_from_pattern(
    pattern: &PatternKind,
    pattern_variant_tags: &PatternVariantTags,
    pattern_qualified_tags: &QualifiedPatternVariantTags,
) -> Option<LiteralCasePatternInfo> {
    match pattern {
        PatternKind::Lit(lit @ Lit::Int(_))
        | PatternKind::Lit(lit @ Lit::Float(_))
        | PatternKind::Lit(lit @ Lit::Bool(_)) => {
            Some((
                vec![literal_case_value_from_lit(lit)?],
                None,
                Vec::new(),
                Vec::new(),
            ))
        }
        PatternKind::Constructor {
            name,
            qualifier,
            args,
            rest,
        } if !*rest => {
            let meta = resolve_variant_tag(
                name,
                qualifier.as_ref(),
                pattern_variant_tags,
                pattern_qualified_tags,
            )?;
            if args.len() != meta.arity {
                return None;
            }
            let mut payload_binds = Vec::new();
            let mut payload_checks = Vec::new();
            for (idx, arg) in args.iter().enumerate() {
                if arg.name.is_some() {
                    return None;
                }
                match &arg.pattern.node {
                    PatternKind::Wildcard => {}
                    PatternKind::Var(bind_name) => {
                        if payload_binds.iter().any(|bind: &ConstructorPayloadBind| bind.name == *bind_name) {
                            return None;
                        }
                        payload_binds.push(ConstructorPayloadBind {
                            name: bind_name.clone(),
                            sum_type: meta.sum_type.clone(),
                            variant: name.clone(),
                            field_index: idx,
                            field_ty: meta.field_types.get(idx).cloned().unwrap_or(Type::Dynamic),
                        });
                    }
                    PatternKind::Lit(lit @ Lit::Int(_))
                    | PatternKind::Lit(lit @ Lit::Float(_))
                    | PatternKind::Lit(lit @ Lit::Bool(_)) => {
                        payload_checks.push(ConstructorPayloadCheck {
                            sum_type: meta.sum_type.clone(),
                            variant: name.clone(),
                            field_index: idx,
                            field_ty: meta
                                .field_types
                                .get(idx)
                                .cloned()
                                .unwrap_or(Type::Dynamic),
                            expected: literal_case_value_from_lit(lit)?,
                        });
                    }
                    _ => return None,
                }
            }
            Some((
                vec![LiteralCaseValue::Int(meta.tag)],
                None,
                payload_binds,
                payload_checks,
            ))
        }
        PatternKind::Or(patterns) => {
            let mut values = Vec::new();
            let mut shared_bind_name: Option<String> = None;
            let mut shared_payload_binds: Option<Vec<ConstructorPayloadBind>> = None;
            let mut shared_payload_checks: Option<Vec<ConstructorPayloadCheck>> = None;
            for branch in patterns {
                let (
                    branch_values,
                    branch_bind_name,
                    branch_payload_binds,
                    branch_payload_checks,
                ) =
                    literal_case_values_from_pattern(
                    &branch.node,
                    pattern_variant_tags,
                    pattern_qualified_tags,
                )?;
                match &shared_payload_binds {
                    None => shared_payload_binds = Some(branch_payload_binds.clone()),
                    Some(existing)
                        if payload_binds_or_compatible(existing, &branch_payload_binds) => {}
                    // OR payload patterns are only supported when all branches
                    // agree on the same payload bind sites.
                    _ => return None,
                }
                match &shared_payload_checks {
                    None => shared_payload_checks = Some(branch_payload_checks.clone()),
                    Some(existing)
                        if payload_checks_or_compatible(existing, &branch_payload_checks) => {}
                    // OR literal payload checks are only supported when all
                    // branches agree on payload check sites/values.
                    _ => return None,
                }
                match (&shared_bind_name, branch_bind_name) {
                    (None, None) => {}
                    (None, Some(name)) => shared_bind_name = Some(name),
                    (Some(existing), Some(name)) if existing == &name => {}
                    // Mixed bind/no-bind or mismatched bind names are ambiguous.
                    _ => return None,
                }
                values.extend(branch_values);
            }
            Some((
                values,
                shared_bind_name,
                shared_payload_binds.unwrap_or_default(),
                shared_payload_checks.unwrap_or_default(),
            ))
        }
        PatternKind::As { pattern, name } => {
            let (values, inner_bind_name, inner_payload_binds, inner_payload_checks) =
                literal_case_values_from_pattern(
                    &pattern.node,
                    pattern_variant_tags,
                    pattern_qualified_tags,
                )?;
            if inner_bind_name.is_some() {
                return None;
            }
            if inner_payload_binds
                .iter()
                .any(|payload| payload.name == name.node)
            {
                // Avoid duplicate bindings in a single lowered arm.
                return None;
            }
            Some((
                values,
                Some(name.node.clone()),
                inner_payload_binds,
                inner_payload_checks,
            ))
        }
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_arm_body(
    body: &Expr,
    bind_name: Option<String>,
    payload_binds: Vec<ConstructorPayloadBind>,
    scrutinee_expr: &HirExpr,
    ty_hint: Option<Type>,
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
    pattern_variant_tags: &PatternVariantTags,
    pattern_qualified_tags: &QualifiedPatternVariantTags,
    known_record_defs: &KnownRecordDefs,
) -> HirExpr {
    let lowered_body = lower_expr(
        body,
        ty_hint,
        unit_variant_tags,
        qualified_variant_tags,
        pattern_variant_tags,
        pattern_qualified_tags,
        known_record_defs,
    );
    let mut bind_exprs = build_literal_arm_bindings(
        bind_name.as_deref(),
        &payload_binds,
        scrutinee_expr,
    );
    if bind_exprs.is_empty() {
        return lowered_body;
    }
    bind_exprs.push(lowered_body.clone());
    HirExpr {
        kind: HirExprKind::Block(bind_exprs),
        ty: lowered_body.ty,
        span: lowered_body.span,
    }
}

fn build_literal_arm_bindings(
    bind_name: Option<&str>,
    payload_binds: &[ConstructorPayloadBind],
    scrutinee_expr: &HirExpr,
) -> Vec<HirExpr> {
    let mut bindings = Vec::new();
    if let Some(name) = bind_name {
        bindings.push(HirExpr {
            kind: HirExprKind::Let {
                pattern: HirPattern::Var(name.to_string()),
                value: Box::new(scrutinee_expr.clone()),
            },
            ty: scrutinee_expr.ty.clone(),
            span: scrutinee_expr.span,
        });
    }
    for payload_bind in payload_binds {
        let payload_ty = payload_bind.field_ty.clone();
        let payload_value = HirExpr {
            kind: HirExprKind::SumPayloadAccess {
                expr: Box::new(scrutinee_expr.clone()),
                sum_type: payload_bind.sum_type.clone(),
                variant: payload_bind.variant.clone(),
                field_index: payload_bind.field_index,
            },
            ty: payload_ty.clone(),
            span: scrutinee_expr.span,
        };
        bindings.push(HirExpr {
            kind: HirExprKind::Let {
                pattern: HirPattern::Var(payload_bind.name.clone()),
                value: Box::new(payload_value),
            },
            ty: payload_ty,
            span: scrutinee_expr.span,
        });
    }
    bindings
}

fn payload_binds_or_compatible(
    existing: &[ConstructorPayloadBind],
    candidate: &[ConstructorPayloadBind],
) -> bool {
    existing.len() == candidate.len()
        && existing.iter().zip(candidate.iter()).all(|(left, right)| {
            left.name == right.name
                && left.sum_type == right.sum_type
                && left.field_index == right.field_index
                && left.field_ty == right.field_ty
        })
}

fn payload_checks_or_compatible(
    existing: &[ConstructorPayloadCheck],
    candidate: &[ConstructorPayloadCheck],
) -> bool {
    existing.len() == candidate.len()
        && existing.iter().zip(candidate.iter()).all(|(left, right)| {
            left.sum_type == right.sum_type
                && left.field_index == right.field_index
                && left.field_ty == right.field_ty
                && left.expected == right.expected
        })
}

fn bool_case_fallback_compatible(pattern: &PatternKind) -> bool {
    matches!(pattern, PatternKind::Lit(Lit::Bool(_)) | PatternKind::Wildcard)
}

fn literal_case_value_from_lit(lit: &Lit) -> Option<LiteralCaseValue> {
    match lit {
        Lit::Int(value) => Some(LiteralCaseValue::Int(*value)),
        Lit::Float(value) => Some(LiteralCaseValue::Float(*value)),
        Lit::Bool(value) => Some(LiteralCaseValue::Bool(*value)),
        _ => None,
    }
}

fn literal_case_lit(lit: LiteralCaseValue) -> Lit {
    match lit {
        LiteralCaseValue::Int(value) => Lit::Int(value),
        LiteralCaseValue::Float(value) => Lit::Float(value),
        LiteralCaseValue::Bool(value) => Lit::Bool(value),
    }
}

fn literal_case_type(lit: LiteralCaseValue) -> Type {
    match lit {
        LiteralCaseValue::Int(_) => Type::Int,
        LiteralCaseValue::Float(_) => Type::Float,
        LiteralCaseValue::Bool(_) => Type::Bool,
    }
}

fn resolve_variant_tag(
    name: &str,
    qualifier: Option<&String>,
    pattern_variant_tags: &PatternVariantTags,
    pattern_qualified_tags: &QualifiedPatternVariantTags,
) -> Option<PatternVariantMeta> {
    if let Some(type_name) = qualifier {
        return pattern_qualified_tags
            .get(&(type_name.clone(), name.to_string()))
            .cloned();
    }
    pattern_variant_tags.get(name).cloned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use kea_ast::FileId;
    use kea_syntax::{lex_layout, parse_module};
    use kea_types::{Label, RowVarId, TypeScheme};

    fn parse_module_from_text(source: &str) -> Module {
        let (tokens, warnings) = lex_layout(source, FileId(0)).expect("lexing should succeed");
        assert!(warnings.is_empty(), "unexpected lexer warnings: {warnings:?}");
        parse_module(tokens, FileId(0)).expect("module should parse")
    }

    #[test]
    fn lower_function_uses_bound_function_type() {
        let module = parse_module_from_text("fn id(x: Int) -> Int\n  x");
        let mut env = TypeEnv::new();
        env.bind(
            "id".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::with_effects(
                vec![Type::Int],
                Type::Int,
                EffectRow::pure(),
            ))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        assert_eq!(function.name, "id");
        assert!(function.effects.is_pure());
        assert_eq!(function.ty.to_string(), "(Int) -> Int");
        assert_eq!(function.body.ty, Type::Int);
    }

    #[test]
    fn lower_function_preserves_effectful_signature() {
        let module = parse_module_from_text("fn write(msg: String) -> Unit\n  msg");
        let mut env = TypeEnv::new();
        env.bind(
            "write".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::with_effects(
                vec![Type::String],
                Type::Unit,
                EffectRow::open(vec![(Label::new("IO"), Type::Unit)], RowVarId(0)),
            ))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        assert_eq!(function.ty.to_string(), "(String) -[IO | e0]> ()");
        assert_eq!(function.effects.to_string(), "[IO | e0]");
    }

    #[test]
    fn lower_function_namespaced_field_access_becomes_qualified_var_reference() {
        let module = parse_module_from_text("fn boom() -> Unit\n  Fail.fail(1)");
        let mut env = TypeEnv::new();
        env.bind(
            "boom".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::with_effects(
                vec![],
                Type::Unit,
                EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
            ))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        let HirExprKind::Call { func, .. } = &function.body.kind else {
            panic!("expected call expression");
        };
        assert!(matches!(&func.kind, HirExprKind::Var(name) if name == "Fail::fail"));
    }

    #[test]
    fn lower_function_record_field_access_stays_structured_hir() {
        let module = parse_module_from_text("fn age(user: User) -> Int\n  user.age");
        let mut env = TypeEnv::new();
        env.bind(
            "age".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![Type::Record(kea_types::RecordType {
                    name: "User".to_string(),
                    params: vec![],
                    row: kea_types::RowType::closed(vec![
                        (Label::new("age"), Type::Int),
                        (Label::new("name"), Type::String),
                    ]),
                })],
                Type::Int,
            ))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };
        assert!(matches!(
            function.body.kind,
            HirExprKind::FieldAccess { ref field, .. } if field == "age"
        ));
    }

    #[test]
    fn lower_function_record_literal_stays_structured_hir() {
        let module = parse_module_from_text("record User\n  age: Int\n\nfn make_user() -> User\n  User { age: 42 }");
        let mut env = TypeEnv::new();
        env.bind(
            "make_user".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![],
                Type::Record(kea_types::RecordType {
                    name: "User".to_string(),
                    params: vec![],
                    row: kea_types::RowType::closed(vec![(Label::new("age"), Type::Int)]),
                }),
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "make_user" => Some(function),
                _ => None,
            })
            .expect("expected lowered make_user function");

        assert!(matches!(
            function.body.kind,
            HirExprKind::RecordLit {
                ref record_type,
                ref fields
            } if record_type == "User" && fields.len() == 1 && fields[0].0 == "age"
        ));
    }

    #[test]
    fn lower_function_payload_constructor_stays_structured_hir() {
        let module = parse_module_from_text(
            "type Flag = Yep(Int) | Nope\n\nfn make_flag() -> Flag\n  Yep(1 + 2)",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "make_flag".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![],
                Type::Sum(kea_types::SumType {
                    name: "Flag".to_string(),
                    type_args: vec![],
                    variants: vec![
                        ("Yep".to_string(), vec![Type::Int]),
                        ("Nope".to_string(), vec![]),
                    ],
                }),
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "make_flag" => Some(function),
                _ => None,
            })
            .expect("expected lowered make_flag function");

        assert!(matches!(
            function.body.kind,
            HirExprKind::SumConstructor {
                ref sum_type,
                ref variant,
                tag: 0,
                ref fields
            } if sum_type == "Flag" && variant == "Yep" && fields.len() == 1
                && matches!(fields[0].kind, HirExprKind::Binary { op: BinOp::Add, .. })
        ));
    }

    #[test]
    fn lower_function_recognizes_binary_expressions() {
        let module = parse_module_from_text("fn inc(x: Int) -> Int\n  x + 1");
        let mut env = TypeEnv::new();
        env.bind(
            "inc".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        assert!(matches!(function.body.kind, HirExprKind::Binary { .. }));
    }

    #[test]
    fn lower_function_recognizes_unary_expressions() {
        let module = parse_module_from_text("fn negate(x: Int) -> Int\n  -x");
        let mut env = TypeEnv::new();
        env.bind(
            "negate".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        assert!(matches!(function.body.kind, HirExprKind::Unary { .. }));
    }

    #[test]
    fn lower_function_bool_case_desugars_to_if() {
        let module = parse_module_from_text(
            "fn pick(x: Bool) -> Int\n  case x\n    true -> 1\n    false -> 0",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Bool], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        assert!(matches!(function.body.kind, HirExprKind::If { .. }));
    }

    #[test]
    fn lower_function_bool_case_var_fallback_binds_scrutinee() {
        let module = parse_module_from_text(
            "fn pick(x: Bool) -> Int\n  case x\n    true -> 1\n    b -> if b then 2 else 3",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Bool], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        let HirExprKind::If {
            else_branch: Some(else_branch),
            ..
        } = &function.body.kind
        else {
            panic!("expected bool var fallback to lower to if with else branch");
        };

        let HirExprKind::Block(exprs) = &else_branch.kind else {
            panic!("expected bool var fallback branch to bind scrutinee");
        };
        assert_eq!(exprs.len(), 2);
        assert!(matches!(
            exprs[0].kind,
            HirExprKind::Let {
                pattern: HirPattern::Var(_),
                ..
            }
        ));
    }

    #[test]
    fn lower_function_bool_case_var_fallback_with_expression_scrutinee_uses_single_binding() {
        let module = parse_module_from_text(
            "fn pick(x: Bool) -> Int\n  case x == true\n    true -> 1\n    b -> if b then 2 else 3",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Bool], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        let HirExprKind::Block(exprs) = &function.body.kind else {
            panic!("expected expression scrutinee bool case to lower through setup block");
        };
        assert_eq!(exprs.len(), 2);
        assert!(matches!(exprs[0].kind, HirExprKind::Let { .. }));
        assert!(matches!(exprs[1].kind, HirExprKind::If { .. }));
    }

    #[test]
    fn lower_function_int_case_desugars_to_if_chain() {
        let module = parse_module_from_text(
            "fn classify(x: Int) -> Int\n  case x\n    0 -> 10\n    1 -> 11\n    _ -> 20",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        let HirExprKind::If { condition, .. } = &function.body.kind else {
            panic!("expected int case to lower to if expression");
        };
        assert!(matches!(
            condition.kind,
            HirExprKind::Binary { op: BinOp::Eq, .. }
        ));

        let HirExprKind::If {
            else_branch: Some(else_branch),
            ..
        } = &function.body.kind
        else {
            panic!("expected chained int case lowering");
        };
        assert!(matches!(else_branch.kind, HirExprKind::If { .. }));
    }

    #[test]
    fn lower_function_float_case_desugars_to_if_chain() {
        let module = parse_module_from_text(
            "fn classify(x: Float) -> Int\n  case x\n    1.5 -> 10\n    2.5 -> 11\n    _ -> 20",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Float], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        let HirExprKind::If { condition, .. } = &function.body.kind else {
            panic!("expected float case to lower to if expression");
        };
        assert!(matches!(
            condition.kind,
            HirExprKind::Binary { op: BinOp::Eq, .. }
        ));

        let HirExprKind::If {
            else_branch: Some(else_branch),
            ..
        } = &function.body.kind
        else {
            panic!("expected chained float case lowering");
        };
        assert!(matches!(else_branch.kind, HirExprKind::If { .. }));
    }

    #[test]
    fn lower_function_literal_case_expression_scrutinee_uses_single_binding() {
        let module = parse_module_from_text(
            "fn classify(x: Int) -> Int\n  case x + 1\n    2 -> 10\n    _ -> 20",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        let HirExprKind::Block(exprs) = &function.body.kind else {
            panic!("expected expression scrutinee case to lower through block binding");
        };
        assert_eq!(exprs.len(), 2);
        assert!(matches!(exprs[0].kind, HirExprKind::Let { .. }));
        assert!(matches!(exprs[1].kind, HirExprKind::If { .. }));
    }

    #[test]
    fn lower_function_literal_case_var_fallback_binds_scrutinee() {
        let module =
            parse_module_from_text("fn classify(x: Int) -> Int\n  case x\n    0 -> 10\n    n -> n");
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        let HirExprKind::If {
            else_branch: Some(else_branch),
            ..
        } = &function.body.kind
        else {
            panic!("expected var fallback lowering to produce if with else branch");
        };

        let HirExprKind::Block(exprs) = &else_branch.kind else {
            panic!("expected var fallback else branch to bind scrutinee");
        };
        assert_eq!(exprs.len(), 2);
        assert!(matches!(
            exprs[0].kind,
            HirExprKind::Let {
                pattern: HirPattern::Var(_),
                ..
            }
        ));
    }

    #[test]
    fn lower_function_block_tail_propagates_type_hint_for_case() {
        let module = parse_module_from_text(
            "fn mark() -> Unit\n  let x = 1\n  case x\n    0 -> ()",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "mark".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![], Type::Unit))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        let HirExprKind::Block(exprs) = &function.body.kind else {
            panic!("expected function body block");
        };
        assert_eq!(exprs.len(), 2);
        assert!(matches!(exprs[1].kind, HirExprKind::If { .. }));
    }

    #[test]
    fn lower_function_unit_enum_case_desugars_through_literal_path() {
        let module = parse_module_from_text(
            "type Color = Red | Green\nfn pick() -> Int\n  case Color.Red\n    Color.Red -> 1\n    Color.Green -> 2",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        match &function.body.kind {
            HirExprKind::If { .. } => {}
            HirExprKind::Block(exprs) => {
                assert!(matches!(exprs.last().map(|expr| &expr.kind), Some(HirExprKind::If { .. })));
            }
            other => panic!("expected enum case to lower through literal-case path, got {other:?}"),
        }
    }

    #[test]
    fn lower_function_payload_constructor_wildcard_case_desugars_to_if_chain() {
        let module = parse_module_from_text(
            "type Flag = Yep(Int) | Nope\nfn pick(x: Flag) -> Int\n  case x\n    Yep(_) -> 1\n    Nope -> 0",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![Type::Sum(kea_types::SumType {
                    name: "Flag".to_string(),
                    type_args: vec![],
                    variants: vec![
                        ("Yep".to_string(), vec![Type::Int]),
                        ("Nope".to_string(), vec![]),
                    ],
                })],
                Type::Int,
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        match &function.body.kind {
            HirExprKind::If { .. } => {}
            HirExprKind::Block(exprs) => {
                assert!(matches!(exprs.last().map(|expr| &expr.kind), Some(HirExprKind::If { .. })));
            }
            other => panic!(
                "expected payload constructor wildcard case to lower through literal-case path, got {other:?}"
            ),
        }
    }

    #[test]
    fn lower_function_payload_constructor_var_case_binds_payload_slot() {
        let module = parse_module_from_text(
            "type Flag = Yep(Int) | Nope\nfn pick(x: Flag) -> Int\n  case x\n    Yep(n) -> n\n    Nope -> 0",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![Type::Sum(kea_types::SumType {
                    name: "Flag".to_string(),
                    type_args: vec![],
                    variants: vec![
                        ("Yep".to_string(), vec![Type::Int]),
                        ("Nope".to_string(), vec![]),
                    ],
                })],
                Type::Int,
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        let then_branch = match &function.body.kind {
            HirExprKind::If { then_branch, .. } => then_branch,
            other => panic!("expected constructor case to lower to if, got {other:?}"),
        };
        let HirExprKind::Block(exprs) = &then_branch.kind else {
            panic!("expected payload case branch to emit binding block");
        };
        assert_eq!(exprs.len(), 2);
        let HirExprKind::Let { pattern, value } = &exprs[0].kind else {
            panic!("expected first payload branch expr to be let binding");
        };
        assert_eq!(pattern, &HirPattern::Var("n".to_string()));
        let HirExprKind::SumPayloadAccess {
            sum_type,
            variant,
            field_index,
            ..
        } = &value.kind
        else {
            panic!("expected payload binding value to be SumPayloadAccess");
        };
        assert_eq!(sum_type, "Flag");
        assert_eq!(variant, "Yep");
        assert_eq!(*field_index, 0);
    }

    #[test]
    fn lower_function_payload_constructor_as_case_binds_scrutinee_and_payload() {
        let module = parse_module_from_text(
            "type Flag = Yep(Int) | Nope\nfn pick(x: Flag) -> Int\n  case x\n    Yep(n) as whole -> n\n    Nope -> 0",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![Type::Sum(kea_types::SumType {
                    name: "Flag".to_string(),
                    type_args: vec![],
                    variants: vec![
                        ("Yep".to_string(), vec![Type::Int]),
                        ("Nope".to_string(), vec![]),
                    ],
                })],
                Type::Int,
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        let then_branch = match &function.body.kind {
            HirExprKind::If { then_branch, .. } => then_branch,
            other => panic!("expected constructor case to lower to if, got {other:?}"),
        };
        let HirExprKind::Block(exprs) = &then_branch.kind else {
            panic!("expected payload as-pattern branch to emit binding block");
        };
        assert_eq!(exprs.len(), 3);
        let HirExprKind::Let {
            pattern: HirPattern::Var(whole_name),
            ..
        } = &exprs[0].kind
        else {
            panic!("expected first binding to capture as-pattern scrutinee");
        };
        assert_eq!(whole_name, "whole");

        let HirExprKind::Let { pattern, value } = &exprs[1].kind else {
            panic!("expected second payload branch expr to be let binding");
        };
        assert_eq!(pattern, &HirPattern::Var("n".to_string()));
        let HirExprKind::SumPayloadAccess {
            sum_type,
            variant,
            field_index,
            ..
        } = &value.kind
        else {
            panic!("expected payload binding value to be SumPayloadAccess");
        };
        assert_eq!(sum_type, "Flag");
        assert_eq!(variant, "Yep");
        assert_eq!(*field_index, 0);
    }

    #[test]
    fn lower_function_payload_constructor_multi_bind_case_binds_each_payload_slot() {
        let module = parse_module_from_text(
            "type Pair = Pair(Int, Int) | Nope\nfn pick(x: Pair) -> Int\n  case x\n    Pair(a, b) -> a + b\n    Nope -> 0",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![Type::Sum(kea_types::SumType {
                    name: "Pair".to_string(),
                    type_args: vec![],
                    variants: vec![
                        ("Pair".to_string(), vec![Type::Int, Type::Int]),
                        ("Nope".to_string(), vec![]),
                    ],
                })],
                Type::Int,
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        let then_branch = match &function.body.kind {
            HirExprKind::If { then_branch, .. } => then_branch,
            other => panic!("expected constructor case to lower to if, got {other:?}"),
        };
        let HirExprKind::Block(exprs) = &then_branch.kind else {
            panic!("expected multi-payload branch to emit binding block");
        };
        assert!(
            matches!(
                exprs.first().map(|expr| &expr.kind),
                Some(HirExprKind::Let {
                    pattern: HirPattern::Var(name),
                    ..
                }) if name == "a"
            ),
            "expected first payload binding for `a`"
        );
        assert!(
            matches!(
                exprs.get(1).map(|expr| &expr.kind),
                Some(HirExprKind::Let {
                    pattern: HirPattern::Var(name),
                    ..
                }) if name == "b"
            ),
            "expected second payload binding for `b`"
        );
    }

    #[test]
    fn lower_function_payload_constructor_literal_arg_case_uses_payload_condition() {
        let module = parse_module_from_text(
            "type Flag = Yep(Int) | Nope\nfn pick(x: Flag) -> Int\n  case x\n    Yep(7) -> 1\n    Nope -> 0",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![Type::Sum(kea_types::SumType {
                    name: "Flag".to_string(),
                    type_args: vec![],
                    variants: vec![
                        ("Yep".to_string(), vec![Type::Int]),
                        ("Nope".to_string(), vec![]),
                    ],
                })],
                Type::Int,
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        let HirExprKind::If { condition, .. } = &function.body.kind else {
            panic!("expected literal payload constructor case to lower to if");
        };
        assert!(
            matches!(
                condition.kind,
                HirExprKind::Binary { op: BinOp::And, .. }
            ),
            "expected constructor literal payload check to compose tag and payload predicates"
        );
    }

    #[test]
    fn lower_function_payload_constructor_or_case_keeps_shared_payload_binding() {
        let module = parse_module_from_text(
            "type Flag = Yep(Int) | Nope\nfn pick(x: Flag) -> Int\n  case x\n    Yep(n) | Yep(n) -> n + 1\n    Nope -> 0",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![Type::Sum(kea_types::SumType {
                    name: "Flag".to_string(),
                    type_args: vec![],
                    variants: vec![
                        ("Yep".to_string(), vec![Type::Int]),
                        ("Nope".to_string(), vec![]),
                    ],
                })],
                Type::Int,
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        let then_branch = match &function.body.kind {
            HirExprKind::If { then_branch, .. } => then_branch,
            other => panic!("expected constructor OR case to lower to if, got {other:?}"),
        };
        let HirExprKind::Block(exprs) = &then_branch.kind else {
            panic!("expected payload OR branch to emit binding block");
        };
        assert!(
            matches!(
                exprs.first().map(|expr| &expr.kind),
                Some(HirExprKind::Let {
                    pattern: HirPattern::Var(name),
                    ..
                }) if name == "n"
            ),
            "expected payload OR branch to bind shared payload name"
        );
    }

    #[test]
    fn lower_function_payload_constructor_or_case_across_variants_keeps_binding() {
        let module = parse_module_from_text(
            "type Either = Left(Int) | Right(Int) | Nope\nfn pick(x: Either) -> Int\n  case x\n    Left(n) | Right(n) -> n + 1\n    Nope -> 0",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![Type::Sum(kea_types::SumType {
                    name: "Either".to_string(),
                    type_args: vec![],
                    variants: vec![
                        ("Left".to_string(), vec![Type::Int]),
                        ("Right".to_string(), vec![Type::Int]),
                        ("Nope".to_string(), vec![]),
                    ],
                })],
                Type::Int,
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        let then_branch = match &function.body.kind {
            HirExprKind::If { then_branch, .. } => then_branch,
            other => panic!("expected constructor OR case to lower to if, got {other:?}"),
        };
        let HirExprKind::Block(exprs) = &then_branch.kind else {
            panic!("expected payload OR branch to emit binding block");
        };
        let HirExprKind::Let { pattern, value } = &exprs[0].kind else {
            panic!("expected first OR branch expression to be payload binding");
        };
        assert_eq!(pattern, &HirPattern::Var("n".to_string()));
        let HirExprKind::SumPayloadAccess { sum_type, field_index, .. } = &value.kind else {
            panic!("expected payload OR branch binding to use SumPayloadAccess");
        };
        assert_eq!(sum_type, "Either");
        assert_eq!(*field_index, 0);
    }

    #[test]
    fn lower_function_payload_constructor_as_guard_binds_before_guard() {
        let module = parse_module_from_text(
            "type Flag = Yep(Int) | Nope\nfn pick(x: Flag) -> Int\n  case x\n    Yep(n) as whole when n == 7 -> n + 1\n    Nope -> 0",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![Type::Sum(kea_types::SumType {
                    name: "Flag".to_string(),
                    type_args: vec![],
                    variants: vec![
                        ("Yep".to_string(), vec![Type::Int]),
                        ("Nope".to_string(), vec![]),
                    ],
                })],
                Type::Int,
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        let HirExprKind::If { condition, .. } = &function.body.kind else {
            panic!("expected payload as+guard case to lower to if expression");
        };
        let HirExprKind::Binary {
            op: BinOp::And,
            right,
            ..
        } = &condition.kind
        else {
            panic!("expected payload as+guard lowering to use and-composed condition");
        };
        let HirExprKind::Block(exprs) = &right.kind else {
            panic!("expected payload as+guard to bind names before guard expression");
        };
        assert!(
            matches!(
                exprs.first().map(|expr| &expr.kind),
                Some(HirExprKind::Let {
                    pattern: HirPattern::Var(name),
                    ..
                }) if name == "whole"
            ),
            "expected first guard binding to capture as-pattern scrutinee"
        );
        assert!(
            matches!(
                exprs.get(1).map(|expr| &expr.kind),
                Some(HirExprKind::Let {
                    pattern: HirPattern::Var(name),
                    ..
                }) if name == "n"
            ),
            "expected second guard binding to capture payload"
        );
    }

    #[test]
    fn lower_function_payload_constructor_or_guard_across_variants_stays_lowered() {
        let module = parse_module_from_text(
            "type Either = Left(Int) | Right(Int) | Nope\nfn pick(x: Either) -> Int\n  case x\n    Left(n) | Right(n) when n > 0 -> n\n    Nope -> 0",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(
                vec![Type::Sum(kea_types::SumType {
                    name: "Either".to_string(),
                    type_args: vec![],
                    variants: vec![
                        ("Left".to_string(), vec![Type::Int]),
                        ("Right".to_string(), vec![Type::Int]),
                        ("Nope".to_string(), vec![]),
                    ],
                })],
                Type::Int,
            ))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        assert!(
            !matches!(function.body.kind, HirExprKind::Raw(_)),
            "expected payload OR guarded case to stay on lowered path"
        );
        let if_count = count_if_nodes(&function.body);
        assert!(
            if_count >= 2,
            "expected payload OR guarded case to lower to >= 2 if nodes, got {if_count}"
        );
    }

    #[test]
    fn lower_function_unit_enum_case_literalized_scrutinee_avoids_setup_block() {
        let module = parse_module_from_text(
            "type Color = Red | Green\nfn pick() -> Int\n  case Color.Red\n    Color.Red -> 1\n    _ -> 2",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        assert!(
            matches!(function.body.kind, HirExprKind::If { .. }),
            "expected literalized unit-enum scrutinee to lower directly to if without setup block"
        );
    }

    #[test]
    fn lower_function_unqualified_unit_enum_case_desugars_through_literal_path() {
        let module = parse_module_from_text(
            "type Color = Red | Green\nfn pick() -> Int\n  case Red\n    Red -> 1\n    Green -> 2",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        match &function.body.kind {
            HirExprKind::If { .. } => {}
            HirExprKind::Block(exprs) => {
                assert!(matches!(exprs.last().map(|expr| &expr.kind), Some(HirExprKind::If { .. })));
            }
            other => panic!(
                "expected unqualified enum case to lower through literal-case path, got {other:?}"
            ),
        }
    }

    #[test]
    fn lower_function_literal_or_pattern_desugars_to_if_chain() {
        let module = parse_module_from_text(
            "fn classify(x: Int) -> Int\n  case x\n    0 | 1 -> 10\n    2 -> 20\n    _ -> 30",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };

        assert!(matches!(function.body.kind, HirExprKind::If { .. }));
        let if_count = count_if_nodes(&function.body);
        assert!(
            if_count >= 3,
            "expected OR pattern to expand into >= 3 if nodes, got {if_count}"
        );
    }

    #[test]
    fn lower_function_unit_enum_or_pattern_desugars_through_literal_path() {
        let module = parse_module_from_text(
            "type Color = Red | Green | Blue\nfn pick() -> Int\n  case Color.Green\n    Color.Red | Color.Green -> 7\n    _ -> 1",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        assert!(matches!(
            function.body.kind,
            HirExprKind::If { .. } | HirExprKind::Block(_)
        ));
        let if_count = count_if_nodes(&function.body);
        assert!(
            if_count >= 2,
            "expected enum OR pattern to expand into >= 2 if nodes, got {if_count}"
        );
    }

    #[test]
    fn lower_function_literal_case_as_pattern_binds_scrutinee() {
        let module =
            parse_module_from_text("fn classify(x: Int) -> Int\n  case x\n    0 as n -> n\n    _ -> 1");
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };
        let HirExprKind::If { then_branch, .. } = &function.body.kind else {
            panic!("expected literal case to lower to if expression");
        };
        let HirExprKind::Block(exprs) = &then_branch.kind else {
            panic!("expected as-pattern arm to bind scrutinee in a block");
        };
        assert!(matches!(
            exprs.first().map(|expr| &expr.kind),
            Some(HirExprKind::Let {
                pattern: HirPattern::Var(_),
                ..
            })
        ));
    }

    #[test]
    fn lower_function_literal_case_guard_desugars_to_and_condition() {
        let module =
            parse_module_from_text("fn classify(x: Int) -> Int\n  case x\n    0 when x == 0 -> 1\n    _ -> 2");
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };
        let HirExprKind::If { condition, .. } = &function.body.kind else {
            panic!(
                "expected literal case with guard to lower to if expression, got {:?}",
                function.body.kind
            );
        };
        assert!(matches!(
            condition.kind,
            HirExprKind::Binary { op: BinOp::And, .. }
        ));
    }

    #[test]
    fn lower_function_literal_case_as_guard_binds_before_guard() {
        let module = parse_module_from_text(
            "fn classify(x: Int) -> Int\n  case x\n    0 as n when n == 0 -> n + 1\n    _ -> 2",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };
        let HirExprKind::If { condition, .. } = &function.body.kind else {
            panic!("expected literal case with as+guard to lower to if expression");
        };
        let HirExprKind::Binary {
            op: BinOp::And,
            right,
            ..
        } = &condition.kind
        else {
            panic!("expected guard lowering to use and-composed condition");
        };
        let HirExprKind::Block(exprs) = &right.kind else {
            panic!("expected as-guard lowering to bind name before guard expression");
        };
        assert!(matches!(
            exprs.first().map(|expr| &expr.kind),
            Some(HirExprKind::Let {
                pattern: HirPattern::Var(_),
                ..
            })
        ));
    }

    #[test]
    fn lower_function_unit_enum_guard_desugars_to_and_condition() {
        let module = parse_module_from_text(
            "type Color = Red | Green\nfn pick() -> Int\n  case Color.Red\n    Color.Red when true -> 1\n    _ -> 2",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        let condition = match &function.body.kind {
            HirExprKind::If { condition, .. } => condition,
            HirExprKind::Block(exprs) => {
                let Some(HirExpr {
                    kind: HirExprKind::If { condition, .. },
                    ..
                }) = exprs.last()
                else {
                    panic!("expected trailing if in lowered unit-enum guarded block");
                };
                condition
            }
            other => panic!(
                "expected unit-enum guarded case to lower to if/block, got {other:?}"
            ),
        };
        assert!(matches!(
            condition.kind,
            HirExprKind::Binary { op: BinOp::And, .. }
        ));
    }

    #[test]
    fn lower_function_unit_enum_as_guard_binds_before_guard() {
        let module = parse_module_from_text(
            "type Color = Red | Green\nfn pick() -> Int\n  case Color.Red\n    Color.Red as c when true -> 1\n    _ -> 2",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        let condition = match &function.body.kind {
            HirExprKind::If { condition, .. } => condition,
            HirExprKind::Block(exprs) => {
                let Some(HirExpr {
                    kind: HirExprKind::If { condition, .. },
                    ..
                }) = exprs.last()
                else {
                    panic!("expected trailing if in lowered unit-enum as+guard block");
                };
                condition
            }
            other => panic!(
                "expected unit-enum as+guard case to lower to if/block, got {other:?}"
            ),
        };
        let HirExprKind::Binary {
            op: BinOp::And,
            right,
            ..
        } = &condition.kind
        else {
            panic!("expected guard lowering to use and-composed condition");
        };
        let HirExprKind::Block(exprs) = &right.kind else {
            panic!("expected as-guard lowering to bind name before guard expression");
        };
        assert!(matches!(
            exprs.first().map(|expr| &expr.kind),
            Some(HirExprKind::Let {
                pattern: HirPattern::Var(_),
                ..
            })
        ));
    }

    #[test]
    fn lower_function_literal_or_guard_desugars_to_and_condition() {
        let module =
            parse_module_from_text("fn classify(x: Int) -> Int\n  case x\n    0 | 1 when true -> 1\n    _ -> 2");
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };
        let HirExprKind::If { condition, .. } = &function.body.kind else {
            panic!("expected literal OR guarded case to lower to if expression");
        };
        assert!(matches!(
            condition.kind,
            HirExprKind::Binary { op: BinOp::And, .. }
        ));
    }

    #[test]
    fn lower_function_unit_enum_or_guard_desugars_to_and_condition() {
        let module = parse_module_from_text(
            "type Color = Red | Green | Blue\nfn pick() -> Int\n  case Color.Red\n    Color.Red | Color.Green when true -> 1\n    _ -> 2",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "pick".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let function = lowered
            .declarations
            .iter()
            .find_map(|decl| match decl {
                HirDecl::Function(function) if function.name == "pick" => Some(function),
                _ => None,
            })
            .expect("expected lowered pick function");

        let condition = match &function.body.kind {
            HirExprKind::If { condition, .. } => condition,
            HirExprKind::Block(exprs) => {
                let Some(HirExpr {
                    kind: HirExprKind::If { condition, .. },
                    ..
                }) = exprs.last()
                else {
                    panic!("expected trailing if in lowered unit-enum OR guarded block");
                };
                condition
            }
            other => panic!(
                "expected unit-enum OR guarded case to lower to if/block, got {other:?}"
            ),
        };
        assert!(matches!(
            condition.kind,
            HirExprKind::Binary { op: BinOp::And, .. }
        ));
    }

    #[test]
    fn lower_function_literal_or_as_pattern_binds_shared_name() {
        let module = parse_module_from_text(
            "fn classify(x: Int) -> Int\n  case x\n    0 as n | 1 as n -> n + 5\n    _ -> 2",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };
        assert!(
            !matches!(function.body.kind, HirExprKind::Raw(_)),
            "expected OR as-pattern with shared name to stay on lowered path"
        );
    }

    #[test]
    fn lower_function_literal_guarded_var_fallback_stays_lowered() {
        let module = parse_module_from_text(
            "fn classify(x: Int) -> Int\n  case x\n    0 -> 1\n    n when n == 1 -> n\n    _ -> 2",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };
        assert!(
            !matches!(function.body.kind, HirExprKind::Raw(_)),
            "expected guarded var fallback case to stay on lowered path"
        );
    }

    #[test]
    fn lower_function_literal_guarded_wildcard_fallback_stays_lowered() {
        let module = parse_module_from_text(
            "fn classify(x: Int) -> Int\n  case x\n    0 -> 1\n    _ when x == 1 -> 2\n    _ -> 3",
        );
        let mut env = TypeEnv::new();
        env.bind(
            "classify".to_string(),
            TypeScheme::mono(Type::Function(FunctionType::pure(vec![Type::Int], Type::Int))),
        );

        let lowered = lower_module(&module, &env);
        let HirDecl::Function(function) = &lowered.declarations[0] else {
            panic!("expected lowered function declaration");
        };
        assert!(
            !matches!(function.body.kind, HirExprKind::Raw(_)),
            "expected guarded wildcard fallback case to stay on lowered path"
        );
    }

    fn count_if_nodes(expr: &HirExpr) -> usize {
        match &expr.kind {
            HirExprKind::If {
                then_branch,
                else_branch,
                ..
            } => 1
                + count_if_nodes(then_branch)
                + else_branch
                    .as_ref()
                    .map(|expr| count_if_nodes(expr))
                    .unwrap_or(0),
            HirExprKind::Block(exprs) | HirExprKind::Tuple(exprs) => {
                exprs.iter().map(count_if_nodes).sum()
            }
            HirExprKind::Binary { left, right, .. } => count_if_nodes(left) + count_if_nodes(right),
            HirExprKind::Unary { operand, .. } => count_if_nodes(operand),
            HirExprKind::Call { func, args } => {
                count_if_nodes(func) + args.iter().map(count_if_nodes).sum::<usize>()
            }
            HirExprKind::RecordLit { fields, .. } => {
                fields.iter().map(|(_, value)| count_if_nodes(value)).sum()
            }
            HirExprKind::SumConstructor { fields, .. } => fields.iter().map(count_if_nodes).sum(),
            HirExprKind::SumPayloadAccess { expr, .. } => count_if_nodes(expr),
            HirExprKind::FieldAccess { expr, .. } => count_if_nodes(expr),
            HirExprKind::Lambda { body, .. } => count_if_nodes(body),
            HirExprKind::Let { value, .. } => count_if_nodes(value),
            HirExprKind::Lit(_) | HirExprKind::Var(_) | HirExprKind::Raw(_) => 0,
        }
    }
}
