//! Typed high-level IR (HIR) for Kea.
//!
//! HIR is the typed/desugared boundary between frontend inference and backend lowering.
//! This initial slice provides a stable typed representation for function declarations
//! and expression trees, with a conservative fallback for unsupported syntax.

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

pub fn lower_module(module: &Module, env: &TypeEnv) -> HirModule {
    let declarations = module
        .declarations
        .iter()
        .map(|decl| match &decl.node {
            DeclKind::Function(fn_decl) => HirDecl::Function(lower_function(fn_decl, env)),
            DeclKind::ExprFn(expr_decl) => {
                HirDecl::Function(lower_function(&expr_decl_to_fn_decl(expr_decl), env))
            }
            other => HirDecl::Raw(other.clone()),
        })
        .collect();
    HirModule { declarations }
}

pub fn lower_function(fn_decl: &FnDecl, env: &TypeEnv) -> HirFunction {
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
        body: lower_expr(&fn_decl.body, Some(ret_ty)),
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

fn lower_expr(expr: &Expr, ty_hint: Option<Type>) -> HirExpr {
    let default_ty = ty_hint.clone().unwrap_or(Type::Dynamic);

    let kind = match &expr.node {
        ExprKind::Lit(lit) => HirExprKind::Lit(lit.clone()),
        ExprKind::Var(name) => HirExprKind::Var(name.clone()),
        ExprKind::BinaryOp { op, left, right } => HirExprKind::Binary {
            op: op.node,
            left: Box::new(lower_expr(left, None)),
            right: Box::new(lower_expr(right, None)),
        },
        ExprKind::UnaryOp { op, operand } => HirExprKind::Unary {
            op: op.node,
            operand: Box::new(lower_expr(operand, None)),
        },
        ExprKind::Call { func, args } => HirExprKind::Call {
            func: Box::new(lower_expr(func, None)),
            args: args
                .iter()
                .map(|arg| lower_expr(&arg.value, None))
                .collect(),
        },
        ExprKind::Lambda { params, body, .. } => HirExprKind::Lambda {
            params: params.iter().map(lower_param).collect(),
            body: Box::new(lower_expr(body, None)),
        },
        ExprKind::Let { pattern, value, .. } => HirExprKind::Let {
            pattern: lower_pattern(pattern),
            value: Box::new(lower_expr(value, None)),
        },
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => HirExprKind::If {
            condition: Box::new(lower_expr(condition, None)),
            then_branch: Box::new(lower_expr(then_branch, ty_hint.clone())),
            else_branch: else_branch
                .as_ref()
                .map(|expr| Box::new(lower_expr(expr, ty_hint.clone()))),
        },
        ExprKind::Case { scrutinee, arms } => {
            if let Some(case_kind) = lower_bool_case(scrutinee, arms, ty_hint.clone()) {
                case_kind
            } else {
                HirExprKind::Raw(expr.node.clone())
            }
        }
        ExprKind::Block(exprs) => HirExprKind::Block(
            exprs
                .iter()
                .map(|inner| lower_expr(inner, None))
                .collect(),
        ),
        ExprKind::Tuple(exprs) => HirExprKind::Tuple(
            exprs
                .iter()
                .map(|inner| lower_expr(inner, None))
                .collect(),
        ),
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
        _ => default_ty,
    };

    HirExpr {
        kind,
        ty,
        span: expr.span,
    }
}

fn lower_bool_case(scrutinee: &Expr, arms: &[CaseArm], ty_hint: Option<Type>) -> Option<HirExprKind> {
    if arms.iter().any(|arm| arm.guard.is_some()) {
        return None;
    }

    if let Some(kind) = lower_literal_case(scrutinee, arms, ty_hint.clone()) {
        return Some(kind);
    }

    if arms.len() == 1
        && matches!(arms[0].pattern.node, PatternKind::Wildcard)
    {
        return Some(lower_expr(&arms[0].body, ty_hint).kind);
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

    let condition = Box::new(lower_expr(scrutinee, None));
    match (true_body, false_body, wildcard_body) {
        (Some(then_body), Some(else_body), None) if arms.len() == 2 => Some(HirExprKind::If {
            condition,
            then_branch: Box::new(lower_expr(then_body, ty_hint.clone())),
            else_branch: Some(Box::new(lower_expr(else_body, ty_hint))),
        }),
        (Some(then_body), None, Some(default_body)) if arms.len() == 2 => Some(HirExprKind::If {
            condition,
            then_branch: Box::new(lower_expr(then_body, ty_hint.clone())),
            else_branch: Some(Box::new(lower_expr(default_body, ty_hint))),
        }),
        (None, Some(else_body), Some(default_body)) if arms.len() == 2 => Some(HirExprKind::If {
            condition,
            then_branch: Box::new(lower_expr(default_body, ty_hint.clone())),
            else_branch: Some(Box::new(lower_expr(else_body, ty_hint))),
        }),
        _ => None,
    }
}

fn lower_literal_case(scrutinee: &Expr, arms: &[CaseArm], ty_hint: Option<Type>) -> Option<HirExprKind> {
    let safe_scrutinee = matches!(scrutinee.node, ExprKind::Var(_) | ExprKind::Lit(_));
    if !safe_scrutinee {
        return None;
    }

    if arms.iter().any(|arm| arm.guard.is_some()) {
        return None;
    }

    let mut literal_arms: Vec<(&Lit, &Expr)> = Vec::new();
    let mut wildcard_body: Option<&Expr> = None;
    for arm in arms {
        match &arm.pattern.node {
            PatternKind::Lit(lit @ Lit::Int(_)) | PatternKind::Lit(lit @ Lit::Bool(_)) => {
                literal_arms.push((lit, &arm.body));
            }
            PatternKind::Wildcard => wildcard_body = Some(&arm.body),
            _ => return None,
        }
    }

    if literal_arms.is_empty() {
        return wildcard_body.map(|body| lower_expr(body, ty_hint).kind);
    }

    let has_true = literal_arms
        .iter()
        .any(|(lit, _)| matches!(lit, Lit::Bool(true)));
    let has_false = literal_arms
        .iter()
        .any(|(lit, _)| matches!(lit, Lit::Bool(false)));
    if wildcard_body.is_none() && (has_true || has_false) {
        // Let the dedicated bool-case lowering path handle exhaustive bool cases
        // without introducing synthetic non-exhaustive branches.
        return None;
    }

    // Non-exhaustive literal chains without a fallback would introduce
    // missing-value paths for non-Unit expressions.
    let _ = wildcard_body.as_ref()?;

    if literal_arms.len() > 1 {
        // Multi-arm literal case lowering needs a dedicated lowering path that
        // preserves value flow across nested joins. Keep this conservative until
        // MIR case lowering lands.
        return None;
    }

    let mut else_expr = wildcard_body.map(|body| lower_expr(body, ty_hint.clone()));
    for (lit, body) in literal_arms.into_iter().rev() {
        let condition = HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::Eq,
                left: Box::new(lower_expr(scrutinee, None)),
                right: Box::new(HirExpr {
                    kind: HirExprKind::Lit(lit.clone()),
                    ty: match lit {
                        Lit::Int(_) => Type::Int,
                        Lit::Bool(_) => Type::Bool,
                        _ => Type::Dynamic,
                    },
                    span: scrutinee.span,
                }),
            },
            ty: Type::Bool,
            span: scrutinee.span,
        };

        let next = HirExpr {
            kind: HirExprKind::If {
                condition: Box::new(condition),
                then_branch: Box::new(lower_expr(body, ty_hint.clone())),
                else_branch: else_expr.as_ref().map(|expr| Box::new(expr.clone())),
            },
            ty: ty_hint.clone().unwrap_or(Type::Dynamic),
            span: scrutinee.span,
        };
        else_expr = Some(next);
    }

    else_expr.map(|expr| expr.kind)
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
            "fn classify(x: Int) -> Int\n  case x\n    0 -> 10\n    _ -> 20",
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
    }
}
