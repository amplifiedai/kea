set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

# Show available tasks.
default:
    @just --list

# Fast check: clippy for changed crates (workspace fallback on root Cargo/tooling changes).
check:
    just lint-fast

# Run all tests.
test:
    #!/usr/bin/env bash
    if ./scripts/cargo-agent.sh nextest --version >/dev/null 2>&1; then
      KEA_ALLOW_WORKSPACE_TESTS=1 ./scripts/cargo-agent.sh nextest run --workspace --lib --tests --bins
    else
      THREADS="${KEA_TEST_THREADS:-2}"
      echo "cargo-nextest not installed; using cargo test with ${THREADS} test threads"
      KEA_ALLOW_WORKSPACE_TESTS=1 ./scripts/cargo-agent.sh test --workspace --lib --tests --bins -- --test-threads "${THREADS}"
    fi

# Run tests only for changed crates (workspace fallback on root Cargo/tooling changes).
test-changed:
    ./scripts/test-changed.sh

# Run all tests for one package: `PKG=<crate> just test-pkg`.
test-pkg:
    #!/usr/bin/env bash
    PKG="${PKG:-}"
    if [ -z "$PKG" ]; then
      echo "usage: PKG=<crate> just test-pkg"
      exit 2
    fi
    if ./scripts/cargo-agent.sh nextest --version >/dev/null 2>&1; then
      ./scripts/cargo-agent.sh nextest run -p "$PKG" --lib --tests --bins
    else
      THREADS="${KEA_TEST_THREADS:-2}"
      echo "cargo-nextest not installed; using cargo test with ${THREADS} test threads"
      ./scripts/cargo-agent.sh test -p "$PKG" --lib --tests --bins -- --test-threads "${THREADS}"
    fi

# Run integration tests for one package: `PKG=<crate> just test-pkg-integration`.
test-pkg-integration:
    #!/usr/bin/env bash
    PKG="${PKG:-}"
    if [ -z "$PKG" ]; then
      echo "usage: PKG=<crate> just test-pkg-integration"
      exit 2
    fi
    if ./scripts/cargo-agent.sh nextest --version >/dev/null 2>&1; then
      ./scripts/cargo-agent.sh nextest run -p "$PKG" --tests
    else
      THREADS="${KEA_TEST_THREADS:-2}"
      echo "cargo-nextest not installed; using cargo test with ${THREADS} test threads"
      ./scripts/cargo-agent.sh test -p "$PKG" --tests -- --test-threads "${THREADS}"
    fi

# Run fast unit/bin tests only.
test-fast:
    #!/usr/bin/env bash
    if ./scripts/cargo-agent.sh nextest --version >/dev/null 2>&1; then
      KEA_ALLOW_WORKSPACE_TESTS=1 ./scripts/cargo-agent.sh nextest run --profile fast --workspace --lib --bins
    else
      THREADS="${KEA_TEST_THREADS_FAST:-2}"
      echo "cargo-nextest not installed; using cargo test with ${THREADS} test threads"
      KEA_ALLOW_WORKSPACE_TESTS=1 ./scripts/cargo-agent.sh test --workspace --lib --bins -- --test-threads "${THREADS}"
    fi

# Run a low-parallelism workspace test pass (memory-safe soak profile).
test-soak:
    #!/usr/bin/env bash
    if ./scripts/cargo-agent.sh nextest --version >/dev/null 2>&1; then
      KEA_ALLOW_WORKSPACE_TESTS=1 ./scripts/cargo-agent.sh nextest run --profile soak --workspace --lib --tests --bins
    else
      THREADS="${KEA_TEST_THREADS_SOAK:-1}"
      echo "cargo-nextest not installed; using cargo test with ${THREADS} test threads"
      KEA_ALLOW_WORKSPACE_TESTS=1 ./scripts/cargo-agent.sh test --workspace --lib --tests --bins -- --test-threads "${THREADS}"
    fi

# Run rustdoc doctests.
test-doc:
    KEA_ALLOW_WORKSPACE_TESTS=1 ./scripts/cargo-agent.sh test --workspace --doc

# Full check including rustdoc doctests.
check-full:
    just lint
    just test
    just test-doc

# Format all Rust code.
fmt:
    ./scripts/cargo-agent.sh fmt --all

# Run clippy with project lints (workspace, all targets).
lint:
    ./scripts/cargo-agent.sh clippy --workspace --all-targets -- -D warnings

# Run clippy for changed crates (workspace fallback on root Cargo/tooling changes).
lint-fast:
    ./scripts/lint-changed.sh

# Show sccache hit/miss stats.
sccache-stats:
    #!/usr/bin/env bash
    if command -v sccache >/dev/null 2>&1; then
      sccache --show-stats
    else
      echo "sccache not installed"
    fi

# Reset sccache stats counters.
sccache-zero:
    #!/usr/bin/env bash
    if command -v sccache >/dev/null 2>&1; then
      sccache --zero-stats
    else
      echo "sccache not installed"
    fi

# Install cargo-nextest if missing.
nextest-install:
    #!/usr/bin/env bash
    if ./scripts/cargo-agent.sh nextest --version >/dev/null 2>&1; then
      cargo nextest --version
    else
      cargo install cargo-nextest --locked
    fi

# Run compiler microbenchmarks.
bench:
    ./scripts/cargo-agent.sh bench -p kea-bench --bench core

# Run benchmarks and export stable artifacts (raw + csv + json + meta).
bench-export:
    ./scripts/bench-export.sh benchmark-results/latest

# Run repeated benchmark exports and summarize median timing variance.
bench-variance:
    ./scripts/bench-variance.sh 3 benchmark-results/variance

# Run whole-program benchmark corpus with hyperfine (fallback runner if missing).
bench-programs:
    ./scripts/bench-programs.sh benchmarks/programs benchmark-results/programs/latest

# Run whole-program benchmarks and compare means against configured baseline thresholds.
bench-programs-regression:
    ./scripts/bench-programs.sh benchmarks/programs benchmark-results/programs-regression/latest && ./scripts/bench-program-threshold-check.sh benchmark-results/programs-regression/latest/hyperfine.json benchmarks/baselines/program-bench-thresholds.csv benchmark-results/programs-regression/latest

# Run whole-program benchmarks and compare means against stable-class blocking thresholds.
bench-programs-regression-stable:
    ./scripts/bench-programs.sh benchmarks/programs benchmark-results/programs-regression-stable/latest && ./scripts/bench-program-threshold-check.sh benchmark-results/programs-regression-stable/latest/hyperfine.json benchmarks/baselines/program-bench-thresholds-stable.csv benchmark-results/programs-regression-stable/latest

# Run repeated whole-program benchmark runs and summarize mean-runtime variance.
bench-programs-variance:
    ./scripts/bench-programs-variance.sh 3 benchmark-results/programs-variance

# Run microbench export and compare medians against configured Stage B baseline thresholds.
bench-regression:
    ./scripts/bench-export.sh benchmark-results/regression/latest && ./scripts/bench-threshold-check.sh benchmark-results/regression/latest/divan.summary.csv benchmarks/baselines/microbench-thresholds.csv benchmark-results/regression/latest

# Run microbench export and compare medians against stable-class blocking thresholds.
bench-regression-stable:
    ./scripts/bench-export.sh benchmark-results/regression-stable/latest && ./scripts/bench-threshold-check.sh benchmark-results/regression-stable/latest/divan.summary.csv benchmarks/baselines/microbench-thresholds-stable.csv benchmark-results/regression-stable/latest

# Run microbench export and enforce update-fusion chained-vs-single benchmark contract.
bench-update-fusion-contract:
    ./scripts/bench-export.sh benchmark-results/update-fusion/latest && ./scripts/bench-update-fusion-contract.sh benchmark-results/update-fusion/latest/divan.summary.csv benchmark-results/update-fusion/latest/update-fusion.contract.md
