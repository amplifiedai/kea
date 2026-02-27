# Brief: Benchmark Infrastructure

**Status:** active
**Priority:** v1-critical (0d prerequisite for performance-backend-strategy)
**Depends on:** 0d-codegen-pure (needs compilable programs to benchmark)
**Blocks:** performance-backend-strategy (benchmark gates require harness), 0e regression gates

## Motivation

The performance-backend-strategy brief defines *what* to measure and
*what thresholds to enforce*. This brief defines *how* — the concrete
tooling, harness design, CI integration, and benchmark corpus that
makes performance work rigorous instead of anecdotal.

Without this, performance claims are stories. With it, they're numbers.

## Framework Selection

### Primary: Divan

[divan](https://github.com/nvzqz/divan) is the right primary framework:

- **AllocProfiler**: built-in allocation counting per benchmark.
  Critical for a refcounted language — we need to know when a
  change increases allocations.
- **Parameterised benchmarks**: `#[divan::bench(args = [1, 4, 16, 64])]`
  maps directly to "effect dispatch at depth N" and "type inference
  on M-node expression trees."
- **Adaptive sample scaling**: auto-tunes for CI without hand-config.
- **Stable Rust**: no nightly required.
- **CodSpeed compatible**: same benchmarks run as wall-time locally,
  instruction-count in CI.

### CI Regression: CodSpeed

[CodSpeed](https://codspeed.io) — free for open source:

- Drop-in via `codspeed-divan-compat` crate. Zero code changes.
- Uses Valgrind-based instruction counting (same philosophy as
  rustc-perf: instruction count is stable, wall time is not).
- Posts regression reports directly to PRs.
- Hardware-agnostic: results comparable across CI machines.

### Sensitive Passes: iai-callgrind

[iai-callgrind](https://github.com/iai-callgrind/iai-callgrind) for
the most critical hot paths (unifier, row solver, codegen lowering):

- Instruction count, cache misses, branch mispredictions.
- One instruction change = one number change. Zero noise.
- Linux CI only (Valgrind requirement).
- Same metric philosophy as rustc's primary benchmark signal.

### End-to-End Compile Time: hyperfine

[hyperfine](https://github.com/sharkdp/hyperfine) wrapping `kea build`
and `kea run` for real-world compile-time measurement.

## Benchmark Corpus

### Tier 1: Microbenchmarks (divan)

Located in `crates/kea-bench/benches/` or per-crate `benches/` dirs.

| Benchmark | What it measures | Phase |
|-----------|-----------------|-------|
| `lexer.rs` | Tokenisation throughput, parameterised on input size | 0d |
| `parser.rs` | Parse time, AST node count | 0d |
| `infer.rs` | Unification iterations, effect row solving | 0d |
| `codegen.rs` | Compile time per function, MIR lowering | 0d |
| `refcount.rs` | Retain/release overhead, allocation count | 0d |
| `update_fusion.rs` | Chained `~` vs single `~` | 0d |
| `effects.rs` | Direct call vs evidence passing vs CPS, parameterised by handler depth | 0e |
| `handler_inline.rs` | Statically-known handler vs dynamic dispatch | 0e |
| `fail_path.rs` | Fail-only (Result branch) vs generic handler dispatch | 0e |
| `reuse.rs` | Allocation count with/without reuse analysis | 0f |
| `unique.rs` | Unique T mutation vs refcounted mutation | 0f |
| `unboxed.rs` | @unboxed flat layout vs heap-allocated | 0f |

Each benchmark uses `AllocProfiler` to track allocation count
alongside wall time.

### Tier 2: Whole-Program Benchmarks (hyperfine + custom)

Programs in `benchmarks/programs/`:

| Program | What it exercises | Phase |
|---------|------------------|-------|
| `fib.kea` | Pure numeric recursion baseline | 0d |
| `sort.kea` | Collection transform, allocation pattern | 0d |
| `json_parse.kea` | String processing, Fail effect, real-world pattern | 0e |
| `state_counter.kea` | State effect tight loop (10^6 iterations) | 0e |
| `actor_pingpong.kea` | Message throughput, 2 actors | 0e+ |
| `compiler_subset.kea` | AST/type-inference-style workload | Phase 1 |

Measured with hyperfine: `hyperfine 'kea run benchmarks/programs/fib.kea'`

### Tier 3: Compiler Self-Benchmarks

When self-hosting: how fast does kea compile itself?
- `kea build` time on the kea codebase
- Incremental rebuild time (one file changed)
- Memory high-water mark during compilation

## CI Integration

### Per-PR Gates (CodSpeed)

```yaml
# .github/workflows/bench.yml
- uses: CodSpeedHQ/action@v3
  with:
    run: cargo codspeed build && cargo codspeed run
```

CodSpeed posts a comment on each PR with:
- Regression/improvement percentages per benchmark
- Flagged regressions above threshold
- Historical trend links

**OIDC setup note (current Kea config):**
- `.github/workflows/bench-codspeed.yml` is configured for OIDC auth
  (no static `CODSPEED_TOKEN` input).
- Repo must be linked in CodSpeed with GitHub OIDC trust enabled for
  this workflow to report metrics.
- Workflow permissions must include `id-token: write` and `contents: read`.

### Threshold Policy

Start permissive, tighten as measurements stabilise:

| Phase | Regression threshold | Action |
|-------|---------------------|--------|
| 0d (establishing baselines) | No gates, record only | Baselines stored |
| 0e (handler compilation) | >15% regression flags PR | Review required |
| 0f+ (stable) | >5% regression blocks PR | Must fix or justify |

### Optimization Contract Verification

The benchmark suite must verify the optimization contracts from
0d and 0f briefs:

| Contract | Benchmark | Gate |
|----------|-----------|------|
| Pure = C-competitive tight loops | `fib.kea` vs C equivalent | Within 2x |
| Fail-only ≈ pure (non-error path) | `fail_path.rs` | Within 5% of pure |
| Tail-resumptive within 2x of direct call | `effects.rs` at depth=1 | Within 2x |
| Unique = zero overhead vs raw mutation | `unique.rs` | Within 5% |
| Reuse-hit within 10% of Unique | `reuse.rs` linear patterns | Within 10% |
| @unboxed = C struct by-value | `unboxed.rs` | Within 5% |

## Cargo Integration

```toml
# Cargo.toml (workspace)
[workspace.dependencies]
divan = "0.1"

# crates/kea-bench/Cargo.toml
[dev-dependencies]
divan = { workspace = true }

[[bench]]
name = "lexer"
harness = false

[[bench]]
name = "parser"
harness = false
```

Example benchmark:

```rust
use divan::AllocProfiler;

#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

fn main() {
    divan::main();
}

#[divan::bench(args = [100, 1000, 10_000])]
fn lex_tokens(bencher: divan::Bencher, n: usize) {
    let src = generate_kea_source(n);
    bencher.bench(|| kea_syntax::lex(&src));
}
```

## mise Tasks

```toml
[tasks.bench]
description = "Run microbenchmarks"
run = "cargo bench -p kea-bench"

[tasks.bench-ci]
description = "Run benchmarks under CodSpeed"
run = "cargo codspeed build -p kea-bench && cargo codspeed run"

[tasks.bench-iai]
description = "Run instruction-count benchmarks (Linux only)"
run = "cargo bench -p kea-bench-iai"

[tasks.bench-programs]
description = "Run whole-program benchmarks"
run = "hyperfine --warmup 3 'kea run benchmarks/programs/*.kea'"
```

## Implementation Plan

### Step 1: Harness setup (0d deliverable)

1. Add `divan` to workspace dependencies
2. Create initial benchmark files (lexer, parser, infer)
3. Set up `AllocProfiler`
4. Add `mise run bench` task
5. Record initial baselines

### Step 2: CI integration

1. Set up CodSpeed GitHub Action
2. Configure `codspeed-divan-compat`
3. Record-only mode (no gates yet)
4. Verify stable measurements across CI runs

### Step 3: Whole-program benchmarks (post-0d)

1. Create `benchmarks/programs/` corpus
2. Set up hyperfine automation
3. Add `mise run bench-programs` task

### Step 4: Regression gates (0e+)

1. Configure CodSpeed thresholds
2. Add optimization contract verification benchmarks
3. Enable PR blocking on regression

## Definition of Done

- divan benchmarks exist for lexer, parser, infer, codegen
- AllocProfiler tracks allocation count per benchmark
- CodSpeed CI integration posts regression reports on PRs
- `mise run bench` works locally
- Baselines recorded for all Tier 1 benchmarks
- Optimization contract benchmarks exist (even if gates aren't active yet)

## Open Questions

- Should iai-callgrind benchmarks live in the same crate or a
  separate `kea-bench-iai` crate? (Proposal: separate crate,
  since iai-callgrind has different harness requirements and
  only runs on Linux.)
- When should we add the actor benchmarks from performance-backend-strategy?
  (Proposal: when the actor runtime exists in 0e+. Placeholder
  benchmark files can exist earlier.)
- Should we track compile-time benchmarks (how fast kea compiles
  programs) separately from runtime benchmarks (how fast compiled
  programs run)? (Proposal: yes. Compile-time is hyperfine on
  `kea build`. Runtime is divan on compiled functions. Different
  regression profiles.)

## Progress
- 2026-02-26: Step 1 harness bootstrap started and partially landed in code: `divan` added to workspace dependencies, `crates/kea-bench` created with `AllocProfiler` and initial microbenchmarks (`lex_parse_numeric_module`, `lower_hir_to_mir`, `compile_numeric_hir_jit`), and `mise run bench` task added.
- 2026-02-26: First local baselines recorded from `mise run bench` (medians): lex+parse `26.65µs` (32), `98.31µs` (128), `386.4µs` (512); HIR→MIR `437.6ns` (16), `1.854µs` (64), `6.984µs` (256); HIR→JIT compile `41.38µs` (8), `94.28µs` (32), `153.1µs` (64).
- 2026-02-26: Stable artifact export landed via `scripts/bench-export.sh`: each run now emits `divan.raw.txt`, `divan.summary.csv`, `divan.summary.json`, and `meta.json` (git SHA + machine/context), with `mise run bench:export` support.
- 2026-02-26: CI Stage A landed in `.github/workflows/bench-stage-a.yml`: benchmarks run on PR/push/workflow_dispatch and artifacts are uploaded; no regression fail gates yet.
- 2026-02-26: Benchmark corpus expanded to cover additional 0d workload classes in `kea-bench`: string-transform-shaped source lex/parse benchmark plus allocation-heavy HIR lowering and compile paths.
- 2026-02-26: Variance characterization automation landed: `scripts/bench-variance.sh` runs repeated exports and writes `variance.summary.csv`/`variance.summary.md`; `mise run bench:variance` and `.github/workflows/bench-variance.yml` publish non-gating CI variance artifacts on `main`.
- 2026-02-26: CodSpeed integration landed in `.github/workflows/bench-codspeed.yml`; bench harness now uses `codspeed-divan-compat` so the same benchmark sources run as normal Divan locally and CodSpeed-instrumented in CI (token-gated until secret is configured).
- 2026-02-26: Whole-program corpus bootstrap landed in `benchmarks/programs/` (`fib`, `case_chain`, `alloc_chain`) with `scripts/bench-programs.sh` and `mise run bench:programs` (hyperfine when available, fallback runner otherwise).
- 2026-02-26: First whole-program local baseline captured via `mise run bench:programs` on this machine (hyperfine means): `fib` ~`2.8ms`, `case_chain` ~`4.0ms`, `alloc_chain` ~`9.4ms`; artifacts at `benchmark-results/programs/latest/hyperfine.{json,md}`.
- 2026-02-26: Tier-1 microbench coverage now includes inference explicitly: `infer_numeric_module` benchmark added to `kea-bench` using row-native typechecking pipeline fixtures (`TypeEnv` + `infer_and_resolve_in_context`) alongside existing lex/parse/lower/codegen benches.
- 2026-02-26: Stage B scaffold landed in non-blocking mode: seeded `benchmarks/baselines/microbench-thresholds.csv`, added `scripts/bench-threshold-check.sh`, wired `mise run bench:regression`, and added `.github/workflows/bench-stage-b.yml` (`continue-on-error`) to publish threshold comparison artifacts without failing PRs.
- 2026-02-26: Whole-program Stage B scaffold landed in non-blocking mode: seeded `benchmarks/baselines/program-bench-thresholds.csv`, added `scripts/bench-program-threshold-check.sh`, wired `mise run bench:programs:regression`, and added `.github/workflows/bench-programs-stage-b.yml` (`continue-on-error`) to publish program regression summaries/artifacts.
- 2026-02-26: Program benchmark runner hardened for lower noise: hyperfine now runs with `--shell=none` via `scripts/run-program-bench.sh` and configurable inner iterations (`BENCH_PROGRAM_INNER_ITERS`, default `10`), removing sub-5ms warning paths and stabilizing baseline means.
- 2026-02-26: Whole-program variance characterization automation landed: `scripts/bench-programs-variance.sh` + `mise run bench:programs:variance` compute per-program spread/CV across repeated runs, and `.github/workflows/bench-programs-variance.yml` publishes variance summaries/artifacts on `main`.
- 2026-02-26: CodSpeed auth migrated to GitHub OIDC-recommended config in `.github/workflows/bench-codspeed.yml` (id-token permissions + no static `CODSPEED_TOKEN` input).
- 2026-02-26: Seed thresholds tightened from bootstrap-wide defaults to narrower non-blocking bands (microbench `50%→35%`, whole-program `60%→40%`) while CI variance history is still accumulating.
- 2026-02-26: Fixed whole-program variance parsing bug (`scripts/bench-programs-variance.sh`) by switching hyperfine extraction from fragile CSV+sed to TSV, restoring correct non-zero mean/CV/spread summaries.
- 2026-02-26: Added stable-class blocking Stage B lanes: `.github/workflows/bench-stage-b-stable.yml` + `.github/workflows/bench-programs-stage-b-stable.yml` with dedicated baselines (`microbench-thresholds-stable.csv`, `program-bench-thresholds-stable.csv`) and local task mirrors (`bench:regression:stable`, `bench:programs:regression:stable`).
- 2026-02-26: Hardened non-blocking Stage B workflows against missing `mise` on CI runners by invoking benchmark scripts directly (same commands as task wrappers), while keeping `Swatinem/rust-cache` dependency caching in place.
- 2026-02-26: Standardized benchmark workflow target-dir env (`KEA_AGENT_TARGET_DIR=target/ci-*`) across CodSpeed/Stage A/Stage B/variance lanes so rust-cache can reuse benchmark build artifacts instead of compiling into ephemeral `/tmp` dirs.
- 2026-02-26: Re-ran local regression + variance sweeps (micro + whole-program), then tightened threshold bands from calibration defaults: non-blocking baselines moved to `30%` (general) / `35%` (noisier string/program lanes), and stable blocking baselines tightened to `20%` (core micro) / `25%` (stable MIR/program lanes). Rechecks against latest runs pass for both blocking and non-blocking threshold sets.
- 2026-02-27 14:16: Consumed CI variance history from the last 12 GitHub Stage B runs (micro + programs), recalibrated all baseline medians to CI medians (`microbench-thresholds*.csv`, `program-bench-thresholds*.csv`), and promoted low-variance parser classes into stable blocking micro gates (`lex_parse_numeric_module` args `128/512`, `lex_parse_string_transform_module` args `64/256`). Verified locally that all four lanes pass with zero failures: `bench:regression`, `bench:regression:stable`, `bench:programs:regression`, `bench:programs:regression:stable`.
- **Next:** Keep collecting CI variance history and only promote additional stable classes after at least one more day of green stable-lane history at the recalibrated baselines.
