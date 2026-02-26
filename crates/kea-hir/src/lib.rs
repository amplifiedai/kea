//! Typed high-level IR (HIR) for Kea.
//!
//! HIR is the typed/desugared boundary between frontend inference and backend lowering.
//! This initial slice provides a stable typed representation for function declarations
//! and expression trees, with a conservative fallback for unsupported syntax.

use kea_ast::{DeclKind, Expr, ExprDecl, ExprKind, FnDecl, Lit, Module, Param, Pattern, PatternKind, Span};
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
        _ => default_ty,
    };

    HirExpr {
        kind,
        ty,
        span: expr.span,
    }
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
}
