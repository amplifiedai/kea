use std::path::PathBuf;

use kea::{compile_module, emit_object};
use kea_ast::FileId;
use kea_codegen::CodegenMode;

struct KernelMetric {
    name: &'static str,
    reuse_count: usize,
    reuse_token_candidate_count: usize,
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
    ];
    let total_reuse: usize = metrics.iter().map(|m| m.reuse_count).sum();
    let total_reuse_token_candidates: usize =
        metrics.iter().map(|m| m.reuse_token_candidate_count).sum();
    let total_alloc: usize = metrics.iter().map(|m| m.alloc_count).sum();
    let total_release: usize = metrics.iter().map(|m| m.release_count).sum();
    let json = render_metrics_json(
        &metrics,
        total_reuse,
        total_reuse_token_candidates,
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
        alloc_count,
        release_count,
    })
}

fn render_metrics_json(
    metrics: &[KernelMetric],
    total_reuse: usize,
    total_reuse_token_candidates: usize,
    total_alloc: usize,
    total_release: usize,
) -> String {
    let kernel_rows = metrics
        .iter()
        .map(|metric| {
            format!(
                "    {{\"name\":\"{}\",\"reuse_count\":{},\"reuse_token_candidate_count\":{},\"alloc_count\":{},\"release_count\":{}}}",
                metric.name,
                metric.reuse_count,
                metric.reuse_token_candidate_count,
                metric.alloc_count,
                metric.release_count
            )
        })
        .collect::<Vec<_>>()
        .join(",\n");

    format!(
        "{{\n  \"kernels\": [\n{kernel_rows}\n  ],\n  \"totals\": {{\"reuse_count\": {total_reuse}, \"reuse_token_candidate_count\": {total_reuse_token_candidates}, \"alloc_count\": {total_alloc}, \"release_count\": {total_release}}}\n}}\n"
    )
}
