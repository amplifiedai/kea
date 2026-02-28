use std::hint::black_box;
#[cfg(unix)]
use std::sync::{Mutex, OnceLock};

use divan::{AllocProfiler, Bencher};
use kea::{compile_module, execute_jit};
use kea_ast::{BinOp, DeclKind, FileId, Lit, Module, RecordDef, Span, Spanned, TypeAnnotation};
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

const STATE_COUNT_BENCH_N: usize = 1_000_000;
const IO_STDOUT_BENCH_WRITES: usize = 1_000;

fn main() {
    divan::main();
}

#[divan::bench(args = [32, 128, 512])]
fn lex_parse_numeric_module(bencher: Bencher, line_count: usize) {
    let source = build_numeric_source(line_count);
    bencher.bench(|| {
        let (tokens, warnings) = lex_layout(black_box(&source), FileId(0))
            .unwrap_or_else(|diags| panic!("lexing failed in benchmark setup: {diags:?}"));
        assert!(
            warnings.is_empty(),
            "unexpected lexer warnings: {warnings:?}"
        );
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
        assert!(
            warnings.is_empty(),
            "unexpected lexer warnings: {warnings:?}"
        );
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
                &expr, &mut env, &mut ctx, &records, &traits, &sum_types,
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

#[divan::bench(args = [8, 32, 128])]
fn lower_linear_heap_alias_chain_to_mir(bencher: Bencher, levels: usize) {
    let hir = build_linear_heap_alias_chain_hir_module(levels);
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

#[divan::bench(args = [8, 32, 128])]
fn compile_linear_heap_alias_chain_hir_jit(bencher: Bencher, levels: usize) {
    let hir = build_linear_heap_alias_chain_hir_module(levels);
    let backend = CraneliftBackend;
    let config = BackendConfig::default();
    bencher.bench(|| {
        let artifact = compile_hir_module(&backend, black_box(&hir), &config)
            .unwrap_or_else(|err| panic!("codegen failed in benchmark setup: {err}"));
        black_box(artifact.stats.per_function.len())
    });
}

#[divan::bench]
fn state_count_to_1_m(bencher: Bencher) {
    let source = build_state_count_to_source(STATE_COUNT_BENCH_N);
    let ctx = compile_module(&source, FileId(0))
        .unwrap_or_else(|err| panic!("state benchmark setup should compile: {err}"));
    bencher.bench(|| {
        let run = execute_jit(black_box(&ctx))
            .unwrap_or_else(|err| panic!("state benchmark run should succeed: {err}"));
        assert_eq!(run.exit_code, STATE_COUNT_BENCH_N as i32);
        black_box(run.exit_code)
    });
}

#[divan::bench]
fn state_count_to_1_m_manual(bencher: Bencher) {
    let source = build_manual_count_to_source(STATE_COUNT_BENCH_N);
    let ctx = compile_module(&source, FileId(0))
        .unwrap_or_else(|err| panic!("manual state benchmark setup should compile: {err}"));
    bencher.bench(|| {
        let run = execute_jit(black_box(&ctx))
            .unwrap_or_else(|err| panic!("manual state benchmark run should succeed: {err}"));
        assert_eq!(run.exit_code, STATE_COUNT_BENCH_N as i32);
        black_box(run.exit_code)
    });
}

#[divan::bench(args = [8, 32, 128])]
fn fail_propagation_depth_n(bencher: Bencher, depth: usize) {
    let source = build_fail_propagation_source(depth);
    let ctx = compile_module(&source, FileId(0))
        .unwrap_or_else(|err| panic!("fail propagation benchmark setup should compile: {err}"));
    bencher.bench(|| {
        let run = execute_jit(black_box(&ctx))
            .unwrap_or_else(|err| panic!("fail propagation benchmark run should succeed: {err}"));
        assert_eq!(run.exit_code, 7);
        black_box(run.exit_code)
    });
}

#[divan::bench(args = [8, 32, 128])]
fn fail_propagation_depth_n_manual_result(bencher: Bencher, depth: usize) {
    let source = build_fail_result_manual_source(depth);
    let ctx = compile_module(&source, FileId(0)).unwrap_or_else(|err| {
        panic!("manual fail/result benchmark setup should compile: {err}")
    });
    bencher.bench(|| {
        let run = execute_jit(black_box(&ctx))
            .unwrap_or_else(|err| panic!("manual fail/result benchmark run should succeed: {err}"));
        assert_eq!(run.exit_code, 7);
        black_box(run.exit_code)
    });
}

#[cfg(unix)]
#[divan::bench]
fn io_stdout_throughput(bencher: Bencher) {
    let source = build_io_stdout_throughput_source(IO_STDOUT_BENCH_WRITES);
    let ctx = compile_module(&source, FileId(0))
        .unwrap_or_else(|err| panic!("io stdout benchmark setup should compile: {err}"));
    bencher.bench(|| {
        let run = with_stdout_redirected_to_dev_null(|| {
            execute_jit(black_box(&ctx))
                .unwrap_or_else(|err| panic!("io stdout benchmark run should succeed: {err}"))
        });
        assert_eq!(run.exit_code, IO_STDOUT_BENCH_WRITES as i32);
        black_box(run.exit_code)
    });
}

#[cfg(unix)]
#[divan::bench]
fn io_stdout_throughput_libc_write(bencher: Bencher) {
    let payload = b"x\n";
    bencher.bench(|| {
        with_stdout_redirected_to_dev_null(|| {
            for _ in 0..IO_STDOUT_BENCH_WRITES {
                // SAFETY: payload is a valid, immutable byte slice and
                // STDOUT is redirected to /dev/null for this benchmark scope.
                let written = unsafe {
                    libc::write(
                        libc::STDOUT_FILENO,
                        payload.as_ptr().cast::<libc::c_void>(),
                        payload.len(),
                    )
                };
                assert!(
                    written >= 0,
                    "libc write failed with errno {}",
                    std::io::Error::last_os_error()
                );
            }
        });
        black_box(IO_STDOUT_BENCH_WRITES)
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

fn build_state_count_to_source(n: usize) -> String {
    format!(
        "effect State S\n  fn get() -> S\n  fn put(next: S) -> Unit\n\nfn count_to(n: Int) -[State Int]> Int\n  let i = State.get()\n  if i >= n\n    i\n  else\n    State.put(i + 1)\n    count_to(n)\n\nfn main() -> Int\n  handle count_to({n})\n    State.get() -> resume 0\n    State.put(s) -> resume ()\n"
    )
}

fn build_manual_count_to_source(n: usize) -> String {
    format!(
        "fn count_to_manual(i: Int, n: Int) -> Int\n  if i >= n\n    i\n  else\n    count_to_manual(i + 1, n)\n\nfn main() -> Int\n  count_to_manual(0, {n})\n"
    )
}

fn build_fail_propagation_source(depth: usize) -> String {
    let depth = depth.max(1);
    let mut source = String::from(
        "effect Fail\n  fn fail(err: Int) -> Never\n\nfn fail_0() -[Fail Int]> Int\n  fail 7\n\n",
    );

    for idx in 1..=depth {
        source.push_str(&format!(
            "fn fail_{idx}() -[Fail Int]> Int\n  fail_{}()\n\n",
            idx - 1
        ));
    }

    source.push_str(&format!(
        "fn main() -> Int\n  let r = catch fail_{depth}()\n  case r\n    Ok(v) -> v\n    Err(e) -> e\n"
    ));
    source
}

fn build_fail_result_manual_source(depth: usize) -> String {
    let depth = depth.max(1);
    let mut source = String::from("fn fail_0_manual() -> Result(Int, Int)\n  Err(7)\n\n");

    for idx in 1..=depth {
        source.push_str(&format!(
            "fn fail_{idx}_manual() -> Result(Int, Int)\n  case fail_{}_manual()\n    Ok(v) -> Ok(v)\n    Err(e) -> Err(e)\n\n",
            idx - 1
        ));
    }

    source.push_str(&format!(
        "fn main() -> Int\n  case fail_{depth}_manual()\n    Ok(v) -> v\n    Err(e) -> e\n"
    ));
    source
}

fn build_io_stdout_throughput_source(writes: usize) -> String {
    format!(
        "effect IO\n  fn stdout(msg: String) -> Unit\n\nfn print_n(n: Int, acc: Int) -[IO]> Int\n  if n == 0\n    acc\n  else\n    IO.stdout(\"x\")\n    print_n(n - 1, acc + 1)\n\nfn main() -> Int\n  print_n({writes}, 0)\n"
    )
}

#[cfg(unix)]
fn with_stdout_redirected_to_dev_null<T>(f: impl FnOnce() -> T) -> T {
    let lock = STDOUT_REDIRECT_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock.lock().expect("stdout redirect lock should be usable");
    let dev_null = std::fs::OpenOptions::new()
        .write(true)
        .open("/dev/null")
        .expect("opening /dev/null should succeed");
    let dev_null_fd = std::os::fd::AsRawFd::as_raw_fd(&dev_null);
    let saved_fd = unsafe { libc::dup(libc::STDOUT_FILENO) };
    assert!(
        saved_fd >= 0,
        "dup stdout failed: {}",
        std::io::Error::last_os_error()
    );
    let dup2_result = unsafe { libc::dup2(dev_null_fd, libc::STDOUT_FILENO) };
    assert!(
        dup2_result >= 0,
        "dup2 stdout->/dev/null failed: {}",
        std::io::Error::last_os_error()
    );
    let out = f();
    let restore_result = unsafe { libc::dup2(saved_fd, libc::STDOUT_FILENO) };
    assert!(
        restore_result >= 0,
        "restoring stdout failed: {}",
        std::io::Error::last_os_error()
    );
    let close_result = unsafe { libc::close(saved_fd) };
    assert!(
        close_result == 0,
        "closing saved stdout fd failed: {}",
        std::io::Error::last_os_error()
    );
    out
}

#[cfg(unix)]
static STDOUT_REDIRECT_LOCK: OnceLock<Mutex<()>> = OnceLock::new();

fn build_numeric_module_ast(line_count: usize) -> Module {
    let source = build_numeric_source(line_count);
    let (tokens, warnings) = lex_layout(&source, FileId(0))
        .unwrap_or_else(|diags| panic!("lexing failed in benchmark setup: {diags:?}"));
    assert!(
        warnings.is_empty(),
        "unexpected lexer warnings: {warnings:?}"
    );
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

fn build_linear_heap_alias_chain_hir_module(levels: usize) -> HirModule {
    let span = Span::synthetic();
    let depth = levels.max(1);
    let box_ty = Type::Record(RecordType {
        name: "Box".to_string(),
        params: vec![],
        row: RowType::closed(vec![(Label::new("n"), Type::Int)]),
    });

    let mut exprs = Vec::with_capacity(depth + 2);
    exprs.push(HirExpr {
        kind: HirExprKind::Let {
            pattern: HirPattern::Var("b0".to_string()),
            value: Box::new(HirExpr {
                kind: HirExprKind::RecordLit {
                    record_type: "Box".to_string(),
                    fields: vec![(
                        "n".to_string(),
                        HirExpr {
                            kind: HirExprKind::Lit(Lit::Int(1)),
                            ty: Type::Int,
                            span,
                        },
                    )],
                },
                ty: box_ty.clone(),
                span,
            }),
        },
        ty: box_ty.clone(),
        span,
    });

    for idx in 1..=depth {
        let prev = format!("b{}", idx - 1);
        let current = format!("b{idx}");
        exprs.push(HirExpr {
            kind: HirExprKind::Let {
                pattern: HirPattern::Var(current),
                value: Box::new(HirExpr {
                    kind: HirExprKind::Var(prev),
                    ty: box_ty.clone(),
                    span,
                }),
            },
            ty: box_ty.clone(),
            span,
        });
    }

    exprs.push(HirExpr {
        kind: HirExprKind::FieldAccess {
            expr: Box::new(HirExpr {
                kind: HirExprKind::Var(format!("b{depth}")),
                ty: box_ty,
                span,
            }),
            field: "n".to_string(),
        },
        ty: Type::Int,
        span,
    });

    let box_record_decl = HirDecl::Raw(DeclKind::RecordDef(RecordDef {
        public: true,
        name: Spanned::new("Box".to_string(), span),
        doc: None,
        annotations: vec![],
        params: vec![],
        fields: vec![(
            Spanned::new("n".to_string(), span),
            TypeAnnotation::Named("Int".to_string()),
        )],
        field_annotations: vec![],
        derives: vec![],
    }));

    HirModule {
        declarations: vec![
            box_record_decl,
            HirDecl::Function(HirFunction {
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
            }),
        ],
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
