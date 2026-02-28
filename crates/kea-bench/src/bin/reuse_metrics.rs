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
    alloc_count: usize,
    release_count: usize,
}

const RECORD_REUSE_SOURCE: &str = r#"struct Point
  x: Int

fn build(n: Int) -> Point
  let p = Point { x: 1 }
  Point { x: n }

fn main() -> Int
  build(7).x
"#;

const SUM_REUSE_SOURCE: &str = r#"type Pairish = Left(Int) | Right(Int)

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

fn main() {
    if let Err(err) = run() {
        eprintln!("{err}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let metrics = vec![
        compile_kernel("record_build", RECORD_REUSE_SOURCE)?,
        compile_kernel("sum_build", SUM_REUSE_SOURCE)?,
        compile_kernel("loop_backedge_rotate", LOOP_BACKEDGE_REUSE_SOURCE)?,
        compile_kernel("recursive_churn", RECURSIVE_CHURN_SOURCE)?,
        compile_kernel("mixed_join_unit", MIXED_JOIN_UNIT_SOURCE)?,
        compile_kernel("loop_mixed_unit_walk", LOOP_MIXED_UNIT_WALK_SOURCE)?,
        compile_kernel("mixed_join_token", MIXED_JOIN_TOKEN_SOURCE)?,
    ];
    let total_reuse: usize = metrics.iter().map(|m| m.reuse_count).sum();
    let total_reuse_token_candidates: usize =
        metrics.iter().map(|m| m.reuse_token_candidate_count).sum();
    let total_reuse_token_produced: usize =
        metrics.iter().map(|m| m.reuse_token_produced_count).sum();
    let total_reuse_token_consumed: usize =
        metrics.iter().map(|m| m.reuse_token_consumed_count).sum();
    let total_alloc: usize = metrics.iter().map(|m| m.alloc_count).sum();
    let total_release: usize = metrics.iter().map(|m| m.release_count).sum();
    let json = render_metrics_json(
        &metrics,
        total_reuse,
        total_reuse_token_candidates,
        total_reuse_token_produced,
        total_reuse_token_consumed,
        total_alloc,
        total_release,
    );

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

fn compile_kernel(name: &'static str, source: &str) -> Result<KernelMetric, String> {
    let ctx = compile_module(source, FileId(0))
        .map_err(|err| format!("failed to compile benchmark kernel `{name}`: {err}"))?;
    let artifact = emit_object(&ctx, CodegenMode::Jit)
        .map_err(|err| format!("failed to lower benchmark kernel `{name}`: {err}"))?;
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
    let alloc_count = artifact.stats.per_function.iter().map(|f| f.alloc_count).sum();
    let release_count = artifact
        .stats
        .per_function
        .iter()
        .map(|f| f.release_count)
        .sum();

    Ok(KernelMetric {
        name,
        reuse_count,
        reuse_token_candidate_count,
        reuse_token_produced_count,
        reuse_token_consumed_count,
        alloc_count,
        release_count,
    })
}

fn render_metrics_json(
    metrics: &[KernelMetric],
    total_reuse: usize,
    total_reuse_token_candidates: usize,
    total_reuse_token_produced: usize,
    total_reuse_token_consumed: usize,
    total_alloc: usize,
    total_release: usize,
) -> String {
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
                "    {{\"name\":\"{}\",\"reuse_count\":{},\"reuse_token_candidate_count\":{},\"reuse_token_produced_count\":{},\"reuse_token_consumed_count\":{},\"reuse_token_coverage_pct\":{:.3},\"alloc_count\":{},\"release_count\":{}}}",
                metric.name,
                metric.reuse_count,
                metric.reuse_token_candidate_count,
                metric.reuse_token_produced_count,
                metric.reuse_token_consumed_count,
                coverage_pct,
                metric.alloc_count,
                metric.release_count
            )
        })
        .collect::<Vec<_>>()
        .join(",\n");

    let total_token_opportunities = total_reuse_token_consumed + total_reuse_token_candidates;
    let total_coverage_pct = if total_token_opportunities > 0 {
        (total_reuse_token_consumed as f64 / total_token_opportunities as f64) * 100.0
    } else {
        0.0
    };

    format!(
        "{{\n  \"kernels\": [\n{kernel_rows}\n  ],\n  \"totals\": {{\"reuse_count\": {total_reuse}, \"reuse_token_candidate_count\": {total_reuse_token_candidates}, \"reuse_token_produced_count\": {total_reuse_token_produced}, \"reuse_token_consumed_count\": {total_reuse_token_consumed}, \"reuse_token_coverage_pct\": {total_coverage_pct:.3}, \"alloc_count\": {total_alloc}, \"release_count\": {total_release}}}\n}}\n"
    )
}
