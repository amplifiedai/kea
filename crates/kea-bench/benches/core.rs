use std::hint::black_box;

use divan::{AllocProfiler, Bencher};
use kea_ast::{BinOp, DeclKind, FileId, Lit, Module, Span};
use kea_codegen::{BackendConfig, CraneliftBackend, compile_hir_module};
use kea_hir::{HirDecl, HirExpr, HirExprKind, HirFunction, HirModule, HirPattern};
use kea_infer::InferenceContext;
use kea_infer::typeck::{
    RecordRegistry, SumTypeRegistry, TraitRegistry, TypeEnv, infer_and_resolve_in_context,
    infer_fn_decl_effect_row, register_fn_effect_signature, register_fn_signature,
};
use kea_mir::lower_hir_module;
use kea_syntax::{lex_layout, parse_module};
use kea_types::{EffectRow, FunctionType, Label, RecordType, RowType, Type};

#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

fn main() {
    divan::main();
}

#[divan::bench(args = [32, 128, 512])]
fn lex_parse_numeric_module(bencher: Bencher, line_count: usize) {
    let source = build_numeric_source(line_count);
    bencher.bench(|| {
        let (tokens, warnings) = lex_layout(black_box(&source), FileId(0))
            .unwrap_or_else(|diags| panic!("lexing failed in benchmark setup: {diags:?}"));
        assert!(warnings.is_empty(), "unexpected lexer warnings: {warnings:?}");
        let module = parse_module(tokens, FileId(0))
            .unwrap_or_else(|diags| panic!("parsing failed in benchmark setup: {diags:?}"));
        black_box(module.declarations.len())
    });
}

#[divan::bench(args = [16, 64, 256])]
fn lex_parse_string_transform_module(bencher: Bencher, line_count: usize) {
    let source = build_string_transform_source(line_count);
    bencher.bench(|| {
        let (tokens, warnings) = lex_layout(black_box(&source), FileId(0))
            .unwrap_or_else(|diags| panic!("lexing failed in benchmark setup: {diags:?}"));
        assert!(warnings.is_empty(), "unexpected lexer warnings: {warnings:?}");
        let module = parse_module(tokens, FileId(0))
            .unwrap_or_else(|diags| panic!("parsing failed in benchmark setup: {diags:?}"));
        black_box(module.declarations.len())
    });
}

#[divan::bench(args = [16, 64, 256])]
fn lower_hir_to_mir(bencher: Bencher, terms: usize) {
    let hir = build_numeric_hir_module(terms);
    bencher.bench(|| {
        let mir = lower_hir_module(black_box(&hir));
        black_box(mir.functions.len())
    });
}

#[divan::bench(args = [16, 64, 256])]
fn infer_numeric_module(bencher: Bencher, line_count: usize) {
    let module = build_numeric_module_ast(line_count);
    bencher.bench(|| {
        let mut env = TypeEnv::new();
        let records = RecordRegistry::new();
        let traits = TraitRegistry::new();
        let sum_types = SumTypeRegistry::new();

        let mut inferred_fns = 0usize;
        for decl in &module.declarations {
            let DeclKind::Function(fn_decl) = &decl.node else {
                continue;
            };

            let mut ctx = InferenceContext::new();
            let expr = fn_decl.to_let_expr();
            let _ = infer_and_resolve_in_context(
                &expr,
                &mut env,
                &mut ctx,
                &records,
                &traits,
                &sum_types,
            );

            if ctx.has_errors() {
                panic!(
                    "type inference failed in benchmark setup: {:?}",
                    ctx.errors()
                );
            }

            let effect_row = infer_fn_decl_effect_row(fn_decl, &env);
            env.set_function_effect_row(fn_decl.name.node.clone(), effect_row);
            register_fn_signature(fn_decl, &mut env);
            register_fn_effect_signature(fn_decl, &mut env);
            inferred_fns += 1;
        }

        black_box(inferred_fns)
    });
}

#[divan::bench(args = [8, 32, 128])]
fn lower_allocation_heavy_hir_to_mir(bencher: Bencher, levels: usize) {
    let hir = build_allocation_heavy_hir_module(levels);
    bencher.bench(|| {
        let mir = lower_hir_module(black_box(&hir));
        black_box(mir.functions.len())
    });
}

#[divan::bench]
fn lower_record_update_single_to_mir(bencher: Bencher) {
    let hir = build_record_update_single_hir_module();
    bencher.bench(|| {
        let mir = lower_hir_module(black_box(&hir));
        black_box(mir.functions.len())
    });
}

#[divan::bench]
fn lower_record_update_chain_to_mir(bencher: Bencher) {
    let hir = build_record_update_chain_hir_module();
    bencher.bench(|| {
        let mir = lower_hir_module(black_box(&hir));
        black_box(mir.functions.len())
    });
}

#[divan::bench(args = [8, 32, 64])]
fn compile_numeric_hir_jit(bencher: Bencher, terms: usize) {
    let hir = build_numeric_hir_module(terms);
    let backend = CraneliftBackend;
    let config = BackendConfig::default();
    bencher.bench(|| {
        let artifact = compile_hir_module(&backend, black_box(&hir), &config)
            .unwrap_or_else(|err| panic!("codegen failed in benchmark setup: {err}"));
        black_box(artifact.stats.per_function.len())
    });
}

#[divan::bench(args = [8, 32, 128])]
fn compile_allocation_heavy_hir_jit(bencher: Bencher, levels: usize) {
    let hir = build_allocation_heavy_hir_module(levels);
    let backend = CraneliftBackend;
    let config = BackendConfig::default();
    bencher.bench(|| {
        let artifact = compile_hir_module(&backend, black_box(&hir), &config)
            .unwrap_or_else(|err| panic!("codegen failed in benchmark setup: {err}"));
        black_box(artifact.stats.per_function.len())
    });
}

fn build_numeric_source(line_count: usize) -> String {
    let mut source = String::from("fn main() -> Int\n");
    if line_count == 0 {
        source.push_str("  0\n");
        return source;
    }

    for idx in 0..line_count {
        source.push_str(&format!("  let x{idx} = {} + {}\n", idx + 1, idx + 2));
    }
    source.push_str(&format!("  x{}\n", line_count - 1));
    source
}

fn build_string_transform_source(line_count: usize) -> String {
    let mut source = String::from("fn main() -> String\n");
    source.push_str("  let seed = \"k\"\n");
    if line_count == 0 {
        source.push_str("  seed\n");
        return source;
    }

    for idx in 0..line_count {
        source.push_str(&format!("  let s{idx} = seed ++ \"{idx}\"\n"));
    }
    source.push_str(&format!("  s{}\n", line_count - 1));
    source
}

fn build_numeric_module_ast(line_count: usize) -> Module {
    let source = build_numeric_source(line_count);
    let (tokens, warnings) = lex_layout(&source, FileId(0))
        .unwrap_or_else(|diags| panic!("lexing failed in benchmark setup: {diags:?}"));
    assert!(warnings.is_empty(), "unexpected lexer warnings: {warnings:?}");
    parse_module(tokens, FileId(0))
        .unwrap_or_else(|diags| panic!("parsing failed in benchmark setup: {diags:?}"))
}

fn build_numeric_hir_module(terms: usize) -> HirModule {
    let span = Span::synthetic();
    let mut expr = HirExpr {
        kind: HirExprKind::Lit(Lit::Int(0)),
        ty: Type::Int,
        span,
    };

    for idx in 1..=terms.max(1) {
        let rhs = HirExpr {
            kind: HirExprKind::Lit(Lit::Int(idx as i64)),
            ty: Type::Int,
            span,
        };
        expr = HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::Add,
                left: Box::new(expr),
                right: Box::new(rhs),
            },
            ty: Type::Int,
            span,
        };
    }

    HirModule {
        declarations: vec![HirDecl::Function(HirFunction {
            name: "main".to_string(),
            params: vec![],
            body: expr,
            ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
            effects: EffectRow::pure(),
            span,
        })],
    }
}

fn build_allocation_heavy_hir_module(levels: usize) -> HirModule {
    let span = Span::synthetic();
    let level_count = levels.max(1);
    let mut exprs = Vec::with_capacity(level_count + 1);
    for idx in 0..level_count {
        let lhs = HirExpr {
            kind: HirExprKind::Lit(Lit::Int(idx as i64)),
            ty: Type::Int,
            span,
        };
        let rhs = HirExpr {
            kind: HirExprKind::Lit(Lit::Int((idx + 1) as i64)),
            ty: Type::Int,
            span,
        };
        let bound_expr = HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::Add,
                left: Box::new(lhs),
                right: Box::new(rhs),
            },
            ty: Type::Int,
            span,
        };
        exprs.push(HirExpr {
            kind: HirExprKind::Let {
                pattern: HirPattern::Var(format!("tmp_{idx}")),
                value: Box::new(bound_expr),
            },
            ty: Type::Int,
            span,
        });
    }

    exprs.push(HirExpr {
        kind: HirExprKind::Var(format!("tmp_{}", level_count - 1)),
        ty: Type::Int,
        span,
    });

    HirModule {
        declarations: vec![HirDecl::Function(HirFunction {
            name: "main".to_string(),
            params: vec![],
            body: HirExpr {
                kind: HirExprKind::Block(exprs),
                ty: Type::Int,
                span,
            },
            ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
            effects: EffectRow::pure(),
            span,
        })],
    }
}

fn build_record_update_single_hir_module() -> HirModule {
    let span = Span::synthetic();
    let user_ty = Type::Record(RecordType {
        name: "User".to_string(),
        params: vec![],
        row: RowType::closed(vec![
            (Label::new("age"), Type::Int),
            (Label::new("score"), Type::Int),
        ]),
    });

    let body = HirExpr {
        kind: HirExprKind::RecordUpdate {
            record_type: "User".to_string(),
            base: Box::new(HirExpr {
                kind: HirExprKind::Var("user".to_string()),
                ty: user_ty.clone(),
                span,
            }),
            fields: vec![
                (
                    "age".to_string(),
                    HirExpr {
                        kind: HirExprKind::Lit(Lit::Int(5)),
                        ty: Type::Int,
                        span,
                    },
                ),
                (
                    "score".to_string(),
                    HirExpr {
                        kind: HirExprKind::Lit(Lit::Int(8)),
                        ty: Type::Int,
                        span,
                    },
                ),
            ],
        },
        ty: user_ty.clone(),
        span,
    };

    HirModule {
        declarations: vec![HirDecl::Function(HirFunction {
            name: "main".to_string(),
            params: vec![kea_hir::HirParam {
                name: Some("user".to_string()),
                span,
            }],
            body,
            ty: Type::Function(FunctionType::pure(vec![user_ty.clone()], user_ty)),
            effects: EffectRow::pure(),
            span,
        })],
    }
}

fn build_record_update_chain_hir_module() -> HirModule {
    let span = Span::synthetic();
    let user_ty = Type::Record(RecordType {
        name: "User".to_string(),
        params: vec![],
        row: RowType::closed(vec![
            (Label::new("age"), Type::Int),
            (Label::new("score"), Type::Int),
        ]),
    });

    let base = HirExpr {
        kind: HirExprKind::Var("user".to_string()),
        ty: user_ty.clone(),
        span,
    };
    let inner = HirExpr {
        kind: HirExprKind::RecordUpdate {
            record_type: "User".to_string(),
            base: Box::new(base),
            fields: vec![(
                "age".to_string(),
                HirExpr {
                    kind: HirExprKind::Lit(Lit::Int(5)),
                    ty: Type::Int,
                    span,
                },
            )],
        },
        ty: user_ty.clone(),
        span,
    };
    let body = HirExpr {
        kind: HirExprKind::RecordUpdate {
            record_type: "User".to_string(),
            base: Box::new(inner),
            fields: vec![(
                "score".to_string(),
                HirExpr {
                    kind: HirExprKind::Lit(Lit::Int(8)),
                    ty: Type::Int,
                    span,
                },
            )],
        },
        ty: user_ty.clone(),
        span,
    };

    HirModule {
        declarations: vec![HirDecl::Function(HirFunction {
            name: "main".to_string(),
            params: vec![kea_hir::HirParam {
                name: Some("user".to_string()),
                span,
            }],
            body,
            ty: Type::Function(FunctionType::pure(vec![user_ty.clone()], user_ty)),
            effects: EffectRow::pure(),
            span,
        })],
    }
}
