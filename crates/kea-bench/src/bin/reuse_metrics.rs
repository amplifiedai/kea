use std::path::PathBuf;

use kea::{compile_module, emit_object};
use kea_ast::FileId;
use kea_codegen::CodegenMode;

struct KernelMetric {
    name: &'static str,
    reuse_count: usize,
    reuse_token_candidate_count: usize,
    reuse_token_produced_count: usize,
    reuse_token_consumed_count: usize,
    stack_sum_mixed_excluded_count: usize,
    trmc_candidate_count: usize,
    alloc_count: usize,
    release_count: usize,
    focus_alloc_count: Option<usize>,
    focus_release_count: Option<usize>,
}

struct KernelSpec {
    name: &'static str,
    source: &'static str,
    focus_functions: &'static [&'static str],
}

struct Totals {
    reuse: usize,
    reuse_token_candidates: usize,
    reuse_token_produced: usize,
    reuse_token_consumed: usize,
    stack_sum_mixed_excluded: usize,
    trmc_candidates: usize,
    alloc: usize,
    release: usize,
}

const RECORD_REUSE_SOURCE: &str = r#"struct Point
  x: Int

fn build(n: Int) -> Point
  let p = Point { x: 1 }
  Point { x: n }

fn main() -> Int
  build(7).x
"#;

const SUM_REUSE_SOURCE: &str = r#"enum Pairish
  Left(Int)
  Right(Int)

fn build(n: Int) -> Pairish
  let p = Left(1)
  Right(n)

fn main() -> Int
  case build(7)
    Right(x) -> x
    Left(x) -> x
"#;

const LOOP_BACKEDGE_REUSE_SOURCE: &str = r#"struct Point
  x: Int

fn rotate(n: Int, p: Point) -> Point
  if n <= 0
    p
  else
    let next = Point { x: n }
    rotate(n - 1, next)

fn main() -> Int
  rotate(8, Point { x: 0 }).x
"#;

const RECURSIVE_CHURN_SOURCE: &str = r#"struct Box
  n: Int

fn churn(i: Int, acc: Int) -> Int
  if i == 0
    acc
  else
    let b = Box { n: i }
    churn(i - 1, acc + b.n - i)

fn main() -> Int
  churn(128, 0)
"#;

const MIXED_SUM_IF_JOIN_SOURCE: &str = r#"fn main() -> Int
  let opt = if 1 == 1
    Some(20)
  else
    None
  case opt
    Some(v) -> v
    None -> 0
"#;

const MIXED_JOIN_UNIT_SOURCE: &str = r#"struct Point
  x: Int

fn consume(flag: Bool, p: Point) -> Unit
  let q = if flag
    p
  else
    Point { x: 1 }
  let out = Point { x: q.x + 1 }
  ()

fn main() -> Int
  consume(true, Point { x: 0 })
  consume(false, Point { x: 0 })
  0
"#;

const LOOP_MIXED_UNIT_WALK_SOURCE: &str = r#"struct Point
  x: Int

fn walk(n: Int, p: Point) -> Unit
  let cur = if n % 2 == 0
    p
  else
    Point { x: p.x + 1 }
  if n <= 0
    ()
  else
    walk(n - 1, cur)

fn main() -> Int
  walk(64, Point { x: 0 })
  0
"#;

const MIXED_JOIN_TOKEN_SOURCE: &str = r#"struct Point
  x: Int

fn rewrite(flag: Bool, p: Point) -> Point
  let merged = if flag
    let tmp = p
    p
  else
    Point { x: 1 }
  Point { x: 9 }

fn main() -> Int
  rewrite(true, Point { x: 0 }).x
"#;

const TRMC_CHAIN_SOURCE: &str = r#"enum Chain
  End
  Node(Int, Chain)

fn build(n: Int) -> Chain
  if n <= 0
    End
  else
    Node(n, build(n - 1))

fn main() -> Int
  case build(4)
    End -> 0
    Node(head, _) -> head
"#;

const TRMC_CHAIN_WEIGHTED_SOURCE: &str = r#"enum Chain
  End
  Node(Int, Chain)

fn build(n: Int) -> Chain
  if n <= 0
    End
  else
    Node(n + n, build(n - 1))

fn main() -> Int
  case build(4)
    End -> 0
    Node(head, _) -> head
"#;

const NO_FOCUS_FUNCTIONS: &[&str] = &[];
const MIXED_JOIN_UNIT_FOCUS_FUNCTIONS: &[&str] = &["consume"];
const LOOP_MIXED_UNIT_WALK_FOCUS_FUNCTIONS: &[&str] = &["walk"];

fn main() {
    if let Err(err) = run() {
        eprintln!("{err}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let metrics = vec![
        compile_kernel(&KernelSpec {
            name: "record_build",
            source: RECORD_REUSE_SOURCE,
            focus_functions: NO_FOCUS_FUNCTIONS,
        })?,
        compile_kernel(&KernelSpec {
            name: "sum_build",
            source: SUM_REUSE_SOURCE,
            focus_functions: NO_FOCUS_FUNCTIONS,
        })?,
        compile_kernel(&KernelSpec {
            name: "loop_backedge_rotate",
            source: LOOP_BACKEDGE_REUSE_SOURCE,
            focus_functions: NO_FOCUS_FUNCTIONS,
        })?,
        compile_kernel(&KernelSpec {
            name: "recursive_churn",
            source: RECURSIVE_CHURN_SOURCE,
            focus_functions: NO_FOCUS_FUNCTIONS,
        })?,
        compile_kernel(&KernelSpec {
            name: "mixed_sum_if_join",
            source: MIXED_SUM_IF_JOIN_SOURCE,
            focus_functions: NO_FOCUS_FUNCTIONS,
        })?,
        compile_kernel(&KernelSpec {
            name: "mixed_join_unit",
            source: MIXED_JOIN_UNIT_SOURCE,
            focus_functions: MIXED_JOIN_UNIT_FOCUS_FUNCTIONS,
        })?,
        compile_kernel(&KernelSpec {
            name: "loop_mixed_unit_walk",
            source: LOOP_MIXED_UNIT_WALK_SOURCE,
            focus_functions: LOOP_MIXED_UNIT_WALK_FOCUS_FUNCTIONS,
        })?,
        compile_kernel(&KernelSpec {
            name: "mixed_join_token",
            source: MIXED_JOIN_TOKEN_SOURCE,
            focus_functions: NO_FOCUS_FUNCTIONS,
        })?,
        compile_kernel(&KernelSpec {
            name: "trmc_chain",
            source: TRMC_CHAIN_SOURCE,
            focus_functions: NO_FOCUS_FUNCTIONS,
        })?,
        compile_kernel(&KernelSpec {
            name: "trmc_chain_weighted",
            source: TRMC_CHAIN_WEIGHTED_SOURCE,
            focus_functions: NO_FOCUS_FUNCTIONS,
        })?,
    ];
    let total_reuse: usize = metrics.iter().map(|m| m.reuse_count).sum();
    let total_reuse_token_candidates: usize =
        metrics.iter().map(|m| m.reuse_token_candidate_count).sum();
    let total_reuse_token_produced: usize =
        metrics.iter().map(|m| m.reuse_token_produced_count).sum();
    let total_reuse_token_consumed: usize =
        metrics.iter().map(|m| m.reuse_token_consumed_count).sum();
    let total_stack_sum_mixed_excluded: usize =
        metrics.iter().map(|m| m.stack_sum_mixed_excluded_count).sum();
    let total_trmc_candidates: usize = metrics.iter().map(|m| m.trmc_candidate_count).sum();
    let totals = Totals {
        reuse: total_reuse,
        reuse_token_candidates: total_reuse_token_candidates,
        reuse_token_produced: total_reuse_token_produced,
        reuse_token_consumed: total_reuse_token_consumed,
        stack_sum_mixed_excluded: total_stack_sum_mixed_excluded,
        trmc_candidates: total_trmc_candidates,
        alloc: metrics.iter().map(|m| m.alloc_count).sum(),
        release: metrics.iter().map(|m| m.release_count).sum(),
    };
    let json = render_metrics_json(&metrics, &totals);

    if let Some(path) = std::env::args().nth(1) {
        let path = PathBuf::from(path);
        if let Some(parent) = path.parent()
            && !parent.as_os_str().is_empty()
        {
            std::fs::create_dir_all(parent)
                .map_err(|err| format!("failed to create `{}`: {err}", parent.display()))?;
        }
        std::fs::write(&path, json)
            .map_err(|err| format!("failed to write `{}`: {err}", path.display()))?;
    } else {
        println!("{json}");
    }

    Ok(())
}

fn compile_kernel(spec: &KernelSpec) -> Result<KernelMetric, String> {
    let ctx = compile_module(spec.source, FileId(0))
        .map_err(|err| format!("failed to compile benchmark kernel `{}`: {err}", spec.name))?;
    let artifact = emit_object(&ctx, CodegenMode::Jit)
        .map_err(|err| format!("failed to lower benchmark kernel `{}`: {err}", spec.name))?;
    let reuse_count = artifact
        .stats
        .per_function
        .iter()
        .map(|f| f.reuse_count)
        .sum();
    let reuse_token_candidate_count = artifact
        .stats
        .per_function
        .iter()
        .map(|f| f.reuse_token_candidate_count)
        .sum();
    let reuse_token_produced_count = artifact
        .stats
        .per_function
        .iter()
        .map(|f| f.reuse_token_produced_count)
        .sum();
    let reuse_token_consumed_count = artifact
        .stats
        .per_function
        .iter()
        .map(|f| f.reuse_token_consumed_count)
        .sum();
    let trmc_candidate_count = artifact
        .stats
        .per_function
        .iter()
        .map(|f| f.trmc_candidate_count)
        .sum();
    let stack_sum_mixed_excluded_count = artifact
        .stats
        .per_function
        .iter()
        .map(|f| f.stack_sum_mixed_excluded_count)
        .sum();
    let alloc_count = artifact
        .stats
        .per_function
        .iter()
        .map(|f| f.alloc_count)
        .sum();
    let release_count = artifact
        .stats
        .per_function
        .iter()
        .map(|f| f.release_count)
        .sum();
    let (focus_alloc_count, focus_release_count) = if spec.focus_functions.is_empty() {
        (None, None)
    } else {
        let focused = artifact
            .stats
            .per_function
            .iter()
            .filter(|f| {
                spec.focus_functions.iter().any(|focus| {
                    f.function == *focus || f.function.ends_with(&format!(".{focus}"))
                })
            })
            .collect::<Vec<_>>();
        if focused.is_empty() {
            (Some(0), Some(0))
        } else {
            (
                Some(focused.iter().map(|f| f.alloc_count).sum()),
                Some(focused.iter().map(|f| f.release_count).sum()),
            )
        }
    };

    Ok(KernelMetric {
        name: spec.name,
        reuse_count,
        reuse_token_candidate_count,
        reuse_token_produced_count,
        reuse_token_consumed_count,
        stack_sum_mixed_excluded_count,
        trmc_candidate_count,
        alloc_count,
        release_count,
        focus_alloc_count,
        focus_release_count,
    })
}

fn render_metrics_json(metrics: &[KernelMetric], totals: &Totals) -> String {
    let kernel_rows = metrics
        .iter()
        .map(|metric| {
            let total_token_opportunities =
                metric.reuse_token_consumed_count + metric.reuse_token_candidate_count;
            let coverage_pct = if total_token_opportunities > 0 {
                (metric.reuse_token_consumed_count as f64 / total_token_opportunities as f64) * 100.0
            } else {
                0.0
            };
            format!(
                "    {{\"name\":\"{}\",\"reuse_count\":{},\"reuse_token_candidate_count\":{},\"reuse_token_produced_count\":{},\"reuse_token_consumed_count\":{},\"reuse_token_coverage_pct\":{:.3},\"stack_sum_mixed_excluded_count\":{},\"trmc_candidate_count\":{},\"alloc_count\":{},\"release_count\":{},\"focus_alloc_count\":{},\"focus_release_count\":{}}}",
                metric.name,
                metric.reuse_count,
                metric.reuse_token_candidate_count,
                metric.reuse_token_produced_count,
                metric.reuse_token_consumed_count,
                coverage_pct,
                metric.stack_sum_mixed_excluded_count,
                metric.trmc_candidate_count,
                metric.alloc_count,
                metric.release_count,
                metric
                    .focus_alloc_count
                    .map(|value| value.to_string())
                    .unwrap_or_else(|| "null".to_string()),
                metric
                    .focus_release_count
                    .map(|value| value.to_string())
                    .unwrap_or_else(|| "null".to_string())
            )
        })
        .collect::<Vec<_>>()
        .join(",\n");

    let total_token_opportunities = totals.reuse_token_consumed + totals.reuse_token_candidates;
    let total_coverage_pct = if total_token_opportunities > 0 {
        (totals.reuse_token_consumed as f64 / total_token_opportunities as f64) * 100.0
    } else {
        0.0
    };

    format!(
        "{{\n  \"kernels\": [\n{kernel_rows}\n  ],\n  \"totals\": {{\"reuse_count\": {}, \"reuse_token_candidate_count\": {}, \"reuse_token_produced_count\": {}, \"reuse_token_consumed_count\": {}, \"reuse_token_coverage_pct\": {total_coverage_pct:.3}, \"stack_sum_mixed_excluded_count\": {}, \"trmc_candidate_count\": {}, \"alloc_count\": {}, \"release_count\": {}}}\n}}\n",
        totals.reuse,
        totals.reuse_token_candidates,
        totals.reuse_token_produced,
        totals.reuse_token_consumed,
        totals.stack_sum_mixed_excluded,
        totals.trmc_candidates,
        totals.alloc,
        totals.release
    )
}
