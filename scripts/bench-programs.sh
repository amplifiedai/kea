#!/usr/bin/env bash
set -euo pipefail

PROGRAM_DIR="${1:-benchmarks/programs}"
OUT_DIR="${2:-benchmark-results/programs/latest}"
RUNS="${BENCH_PROGRAM_RUNS:-10}"
WARMUP="${BENCH_PROGRAM_WARMUP:-2}"
INNER_ITERS="${BENCH_PROGRAM_INNER_ITERS:-10}"

mkdir -p "${OUT_DIR}"

if [ ! -d "${PROGRAM_DIR}" ]; then
  echo "program directory not found: ${PROGRAM_DIR}" >&2
  exit 2
fi

mapfile -t programs < <(find "${PROGRAM_DIR}" -maxdepth 1 -type f -name '*.kea' | sort)
if [ "${#programs[@]}" -eq 0 ]; then
  echo "no .kea benchmark programs found in ${PROGRAM_DIR}" >&2
  exit 2
fi

export KEA_AGENT_TARGET_DIR="${KEA_AGENT_TARGET_DIR:-/tmp/kea-bench-programs-target}"
./scripts/cargo-agent.sh build -p kea --bin kea >/dev/null

KEA_BIN="${KEA_AGENT_TARGET_DIR}/debug/kea"
if [ ! -x "${KEA_BIN}" ]; then
  echo "expected kea binary at ${KEA_BIN}" >&2
  exit 1
fi

echo "Using kea binary: ${KEA_BIN}"
echo "Benchmark programs:"
for program in "${programs[@]}"; do
  echo "  - ${program}"
done

if command -v hyperfine >/dev/null 2>&1; then
  args=()
  for program in "${programs[@]}"; do
    name="$(basename "${program}" .kea)"
    args+=(
      "--command-name" "${name}"
      "./scripts/run-program-bench.sh ${KEA_BIN} ${program} ${INNER_ITERS}"
    )
  done
  hyperfine \
    --shell=none \
    --warmup "${WARMUP}" \
    --runs "${RUNS}" \
    --export-json "${OUT_DIR}/hyperfine.json" \
    --export-markdown "${OUT_DIR}/hyperfine.md" \
    "${args[@]}"
  echo "Wrote:"
  echo "  ${OUT_DIR}/hyperfine.json"
  echo "  ${OUT_DIR}/hyperfine.md"
  exit 0
fi

echo "hyperfine not found; running fallback loop (${RUNS} measured runs/program, ${INNER_ITERS} inner iters/run)."
echo "program,runs,elapsed_seconds" > "${OUT_DIR}/fallback.csv"
for program in "${programs[@]}"; do
  name="$(basename "${program}" .kea)"
  start="$(date +%s)"
  for _ in $(seq 1 "${RUNS}"); do
    ./scripts/run-program-bench.sh "${KEA_BIN}" "${program}" "${INNER_ITERS}"
  done
  end="$(date +%s)"
  elapsed="$((end - start))"
  echo "${name},${RUNS},${elapsed}" | tee -a "${OUT_DIR}/fallback.csv"
done

echo "Wrote:"
echo "  ${OUT_DIR}/fallback.csv"
