use std::hint::black_box;

use divan::{AllocProfiler, Bencher};
use kea_ast::{BinOp, FileId, Lit, Span};
use kea_codegen::{BackendConfig, CraneliftBackend, compile_hir_module};
use kea_hir::{HirDecl, HirExpr, HirExprKind, HirFunction, HirModule};
use kea_mir::lower_hir_module;
use kea_syntax::{lex_layout, parse_module};
use kea_types::{EffectRow, FunctionType, Type};

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
fn lower_hir_to_mir(bencher: Bencher, terms: usize) {
    let hir = build_numeric_hir_module(terms);
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
