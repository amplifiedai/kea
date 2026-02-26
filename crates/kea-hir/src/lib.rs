//! Typed high-level IR (HIR) for Kea.
//!
//! HIR is the typed/desugared boundary between frontend inference and backend lowering.
//! This initial slice provides a stable typed representation for function declarations
//! and expression trees, with a conservative fallback for unsupported syntax.

use std::collections::{BTreeMap, BTreeSet};

use kea_ast::{
    BinOp, CaseArm, DeclKind, Expr, ExprDecl, ExprKind, FnDecl, Lit, Module, Param, Pattern,
    PatternKind, Span, UnaryOp,
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

fn collect_unit_variant_tags(module: &Module) -> (UnitVariantTags, QualifiedUnitVariantTags) {
    let mut unqualified = UnitVariantTags::new();
    let mut qualified = QualifiedUnitVariantTags::new();
    let mut duplicates = BTreeSet::new();

    for decl in &module.declarations {
        let DeclKind::TypeDef(def) = &decl.node else {
            continue;
        };

        for (idx, variant) in def.variants.iter().enumerate() {
            if !variant.fields.is_empty() {
                continue;
            }

            let tag = idx as i64;
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

    (unqualified, qualified)
}

pub fn lower_module(module: &Module, env: &TypeEnv) -> HirModule {
    let (unit_variant_tags, qualified_variant_tags) = collect_unit_variant_tags(module);
    let declarations = module
        .declarations
        .iter()
        .map(|decl| match &decl.node {
            DeclKind::Function(fn_decl) => HirDecl::Function(lower_function_with_variants(
                fn_decl,
                env,
                &unit_variant_tags,
                &qualified_variant_tags,
            )),
            DeclKind::ExprFn(expr_decl) => HirDecl::Function(lower_function_with_variants(
                &expr_decl_to_fn_decl(expr_decl),
                env,
                &unit_variant_tags,
                &qualified_variant_tags,
            )),
            other => HirDecl::Raw(other.clone()),
        })
        .collect();
    HirModule { declarations }
}

pub fn lower_function(fn_decl: &FnDecl, env: &TypeEnv) -> HirFunction {
    lower_function_with_variants(
        fn_decl,
        env,
        &UnitVariantTags::new(),
        &QualifiedUnitVariantTags::new(),
    )
}

fn lower_function_with_variants(
    fn_decl: &FnDecl,
    env: &TypeEnv,
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
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
            )),
            right: Box::new(lower_expr(
                right,
                None,
                unit_variant_tags,
                qualified_variant_tags,
            )),
        },
        ExprKind::UnaryOp { op, operand } => HirExprKind::Unary {
            op: op.node,
            operand: Box::new(lower_expr(
                operand,
                None,
                unit_variant_tags,
                qualified_variant_tags,
            )),
        },
        ExprKind::Call { func, args } => HirExprKind::Call {
            func: Box::new(lower_expr(
                func,
                None,
                unit_variant_tags,
                qualified_variant_tags,
            )),
            args: args
                .iter()
                .map(|arg| {
                    lower_expr(&arg.value, None, unit_variant_tags, qualified_variant_tags)
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
            )),
        },
        ExprKind::Let { pattern, value, .. } => HirExprKind::Let {
            pattern: lower_pattern(pattern),
            value: Box::new(lower_expr(
                value,
                None,
                unit_variant_tags,
                qualified_variant_tags,
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
            )),
            then_branch: Box::new(lower_expr(
                then_branch,
                ty_hint.clone(),
                unit_variant_tags,
                qualified_variant_tags,
            )),
            else_branch: else_branch
                .as_ref()
                .map(|expr| {
                    Box::new(lower_expr(
                        expr,
                        ty_hint.clone(),
                        unit_variant_tags,
                        qualified_variant_tags,
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
                        lower_expr(inner, hint, unit_variant_tags, qualified_variant_tags)
                    })
                    .collect(),
            )
        }
        ExprKind::Tuple(exprs) => HirExprKind::Tuple(
            exprs
                .iter()
                .map(|inner| lower_expr(inner, None, unit_variant_tags, qualified_variant_tags))
                .collect(),
        ),
        ExprKind::Constructor { name, args } => {
            if args.is_empty() {
                if let Some(tag) = unit_variant_tags.get(&name.node) {
                    HirExprKind::Lit(Lit::Int(*tag))
                } else {
                    HirExprKind::Raw(expr.node.clone())
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
                } else {
                    HirExprKind::Raw(expr.node.clone())
                }
            } else {
                HirExprKind::Raw(expr.node.clone())
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

fn lower_bool_case(
    scrutinee: &Expr,
    arms: &[CaseArm],
    ty_hint: Option<Type>,
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
) -> Option<HirExprKind> {
    if let Some(kind) = lower_literal_case(
        scrutinee,
        arms,
        ty_hint.clone(),
        unit_variant_tags,
        qualified_variant_tags,
    ) {
        return Some(kind);
    }

    if arms.iter().any(|arm| arm.guard.is_some()) {
        return None;
    }

    if arms.len() == 1 && matches!(arms[0].pattern.node, PatternKind::Wildcard) {
        return Some(
            lower_expr(
                &arms[0].body,
                ty_hint,
                unit_variant_tags,
                qualified_variant_tags,
            )
            .kind,
        );
    }

    let mut true_body: Option<&Expr> = None;
    let mut false_body: Option<&Expr> = None;
    let mut wildcard_body: Option<&Expr> = None;

    for arm in arms {
        match &arm.pattern.node {
            PatternKind::Lit(Lit::Bool(true)) => true_body = Some(&arm.body),
            PatternKind::Lit(Lit::Bool(false)) => false_body = Some(&arm.body),
            PatternKind::Wildcard => wildcard_body = Some(&arm.body),
            _ => return None,
        }
    }

    let condition = Box::new(lower_expr(
        scrutinee,
        None,
        unit_variant_tags,
        qualified_variant_tags,
    ));
    match (true_body, false_body, wildcard_body) {
        (Some(then_body), Some(else_body), None) if arms.len() == 2 => Some(HirExprKind::If {
            condition,
            then_branch: Box::new(lower_expr(
                then_body,
                ty_hint.clone(),
                unit_variant_tags,
                qualified_variant_tags,
            )),
            else_branch: Some(Box::new(lower_expr(
                else_body,
                ty_hint,
                unit_variant_tags,
                qualified_variant_tags,
            ))),
        }),
        (Some(then_body), None, Some(default_body)) if arms.len() == 2 => Some(HirExprKind::If {
            condition,
            then_branch: Box::new(lower_expr(
                then_body,
                ty_hint.clone(),
                unit_variant_tags,
                qualified_variant_tags,
            )),
            else_branch: Some(Box::new(lower_expr(
                default_body,
                ty_hint,
                unit_variant_tags,
                qualified_variant_tags,
            ))),
        }),
        (None, Some(else_body), Some(default_body)) if arms.len() == 2 => Some(HirExprKind::If {
            condition,
            then_branch: Box::new(lower_expr(
                default_body,
                ty_hint.clone(),
                unit_variant_tags,
                qualified_variant_tags,
            )),
            else_branch: Some(Box::new(lower_expr(
                else_body,
                ty_hint,
                unit_variant_tags,
                qualified_variant_tags,
            ))),
        }),
        _ => None,
    }
}

fn lower_literal_case(
    scrutinee: &Expr,
    arms: &[CaseArm],
    ty_hint: Option<Type>,
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
) -> Option<HirExprKind> {
    let mut literal_arms: Vec<(LiteralCaseValue, &Expr, Option<String>, Option<&Expr>)> =
        Vec::new();
    let mut wildcard_body: Option<&Expr> = None;
    let mut var_fallback: Option<(String, &Expr)> = None;
    for arm in arms {
        match &arm.pattern.node {
            PatternKind::Wildcard => {
                if arm.guard.is_some() {
                    return None;
                }
                wildcard_body = Some(&arm.body);
            }
            PatternKind::Var(name) => {
                if arm.guard.is_some() {
                    return None;
                }
                var_fallback = Some((name.clone(), &arm.body));
            }
            pattern => {
                let (values, bind_name) = literal_case_values_from_pattern(
                    pattern,
                    unit_variant_tags,
                    qualified_variant_tags,
                )?;
                for value in values {
                    literal_arms.push((value, &arm.body, bind_name.clone(), arm.guard.as_deref()));
                }
            }
        }
    }

    if wildcard_body.is_some() && var_fallback.is_some() {
        return None;
    }

    let has_true = literal_arms
        .iter()
        .any(|(lit, _, _, _)| matches!(lit, LiteralCaseValue::Bool(true)));
    let has_false = literal_arms
        .iter()
        .any(|(lit, _, _, _)| matches!(lit, LiteralCaseValue::Bool(false)));
    if wildcard_body.is_none()
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

    let mut else_expr = if let Some(body) = wildcard_body {
        Some(lower_expr(
            body,
            ty_hint.clone(),
            unit_variant_tags,
            qualified_variant_tags,
        ))
    } else if let Some((name, body)) = var_fallback {
        let fallback_bind = HirExpr {
            kind: HirExprKind::Let {
                pattern: HirPattern::Var(name),
                value: Box::new(scrutinee_expr.clone()),
            },
            ty: scrutinee_expr.ty.clone(),
            span: scrutinee.span,
        };
        Some(HirExpr {
            kind: HirExprKind::Block(vec![
                fallback_bind,
                lower_expr(
                    body,
                    ty_hint.clone(),
                    unit_variant_tags,
                    qualified_variant_tags,
                ),
            ]),
            ty: return_ty.clone(),
            span: scrutinee.span,
        })
    } else {
        None
    };

    if else_expr.is_none() && !literal_arms.is_empty() {
        // Type checking enforces exhaustiveness before lowering. For exhaustive literal
        // chains without an explicit fallback (for example unit-enum constructor cases),
        // provide a defensive synthetic else so non-unit MIR value paths stay closed.
        let (_, fallback_body, _, _) = literal_arms
            .last()
            .expect("checked literal_arms is non-empty");
        else_expr = Some(lower_expr(
            fallback_body,
            ty_hint.clone(),
            unit_variant_tags,
            qualified_variant_tags,
        ));
    }

    if literal_arms.is_empty() {
        let lowered = else_expr?;
        if let Some(setup) = setup_expr {
            return Some(HirExprKind::Block(vec![setup, lowered]));
        }
        return Some(lowered.kind);
    }

    for (lit, body, bind_name, guard) in literal_arms.into_iter().rev() {
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
        if let Some(guard_expr) = guard {
            let lowered_guard = if let Some(name) = bind_name.clone() {
                let bind_expr = HirExpr {
                    kind: HirExprKind::Let {
                        pattern: HirPattern::Var(name),
                        value: Box::new(scrutinee_expr.clone()),
                    },
                    ty: scrutinee_expr.ty.clone(),
                    span: scrutinee_expr.span,
                };
                let guard_expr = lower_expr(
                    guard_expr,
                    None,
                    unit_variant_tags,
                    qualified_variant_tags,
                );
                HirExpr {
                    kind: HirExprKind::Block(vec![bind_expr, guard_expr]),
                    ty: Type::Bool,
                    span: scrutinee.span,
                }
            } else {
                lower_expr(guard_expr, None, unit_variant_tags, qualified_variant_tags)
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
                    &scrutinee_expr,
                    ty_hint.clone(),
                    unit_variant_tags,
                    qualified_variant_tags,
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
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
) -> Option<(Vec<LiteralCaseValue>, Option<String>)> {
    match pattern {
        PatternKind::Lit(lit @ Lit::Int(_))
        | PatternKind::Lit(lit @ Lit::Float(_))
        | PatternKind::Lit(lit @ Lit::Bool(_)) => {
            Some((vec![literal_case_value_from_lit(lit)?], None))
        }
        PatternKind::Constructor {
            name,
            qualifier,
            args,
            rest,
        } if args.is_empty() && !*rest => {
            let tag = resolve_unit_variant_tag(
                name,
                qualifier.as_ref(),
                unit_variant_tags,
                qualified_variant_tags,
            )?;
            Some((vec![LiteralCaseValue::Int(tag)], None))
        }
        PatternKind::Or(patterns) => {
            let mut values = Vec::new();
            for branch in patterns {
                let (branch_values, branch_bind_name) = literal_case_values_from_pattern(
                    &branch.node,
                    unit_variant_tags,
                    qualified_variant_tags,
                )?;
                if branch_bind_name.is_some() {
                    return None;
                }
                values.extend(branch_values);
            }
            Some((values, None))
        }
        PatternKind::As { pattern, name } => {
            let (values, inner_bind_name) = literal_case_values_from_pattern(
                &pattern.node,
                unit_variant_tags,
                qualified_variant_tags,
            )?;
            if inner_bind_name.is_some() {
                return None;
            }
            Some((values, Some(name.node.clone())))
        }
        _ => None,
    }
}

fn lower_arm_body(
    body: &Expr,
    bind_name: Option<String>,
    scrutinee_expr: &HirExpr,
    ty_hint: Option<Type>,
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
) -> HirExpr {
    let lowered_body = lower_expr(body, ty_hint, unit_variant_tags, qualified_variant_tags);
    let Some(name) = bind_name else {
        return lowered_body;
    };
    let bind_expr = HirExpr {
        kind: HirExprKind::Let {
            pattern: HirPattern::Var(name),
            value: Box::new(scrutinee_expr.clone()),
        },
        ty: scrutinee_expr.ty.clone(),
        span: scrutinee_expr.span,
    };
    HirExpr {
        kind: HirExprKind::Block(vec![bind_expr, lowered_body.clone()]),
        ty: lowered_body.ty,
        span: lowered_body.span,
    }
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

fn resolve_unit_variant_tag(
    name: &str,
    qualifier: Option<&String>,
    unit_variant_tags: &UnitVariantTags,
    qualified_variant_tags: &QualifiedUnitVariantTags,
) -> Option<i64> {
    if let Some(type_name) = qualifier {
        return qualified_variant_tags
            .get(&(type_name.clone(), name.to_string()))
            .copied();
    }
    unit_variant_tags.get(name).copied()
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
            HirExprKind::Lambda { body, .. } => count_if_nodes(body),
            HirExprKind::Let { value, .. } => count_if_nodes(value),
            HirExprKind::Lit(_) | HirExprKind::Var(_) | HirExprKind::Raw(_) => 0,
        }
    }
}
