#!/usr/bin/env bash
set -euo pipefail

RUNS="${1:-3}"
OUT_DIR="${2:-benchmark-results/programs-variance}"

if ! [[ "${RUNS}" =~ ^[0-9]+$ ]] || [ "${RUNS}" -lt 2 ]; then
  echo "usage: $0 <runs>=3 <out-dir>=benchmark-results/programs-variance"
  echo "runs must be an integer >= 2"
  exit 2
fi

if ! command -v jq >/dev/null 2>&1; then
  echo "jq is required for program benchmark variance summaries" >&2
  exit 2
fi

RUNS_DIR="${OUT_DIR}/runs"
SUMMARY_CSV="${OUT_DIR}/variance.summary.csv"
SUMMARY_MD="${OUT_DIR}/variance.summary.md"
TMP_ROWS="${OUT_DIR}/rows.tmp.csv"
TMP_SUMMARY="${OUT_DIR}/summary.tmp.csv"

mkdir -p "${RUNS_DIR}"
rm -f "${TMP_ROWS}" "${TMP_SUMMARY}"

echo "Running ${RUNS} whole-program benchmark repetitions for variance characterization..."
for idx in $(seq 1 "${RUNS}"); do
  run_dir="${RUNS_DIR}/run-${idx}"
  echo "  run ${idx}/${RUNS}: ${run_dir}"
  ./scripts/bench-programs.sh benchmarks/programs "${run_dir}"
  jq -r '.results[] | [.command, (.mean|tostring)] | @tsv' "${run_dir}/hyperfine.json" \
    >> "${TMP_ROWS}"
done

awk -F"\t" '
{
  program = $1
  mean = $2 + 0
  count[program] += 1
  sum[program] += mean
  sumsq[program] += mean * mean
  if (!(program in min) || mean < min[program]) min[program] = mean
  if (!(program in max) || mean > max[program]) max[program] = mean
}
END {
  for (program in count) {
    n = count[program]
    avg = sum[program] / n
    variance = (sumsq[program] / n) - (avg * avg)
    if (variance < 0) variance = 0
    stddev = sqrt(variance)
    cv = (avg == 0) ? 0 : (stddev / avg) * 100
    spread = (avg == 0) ? 0 : ((max[program] - min[program]) / avg) * 100
    printf "%s,%d,%.9f,%.9f,%.9f,%.9f,%.3f,%.3f\n",
      program, n, min[program], max[program], avg, stddev, cv, spread
  }
}
' "${TMP_ROWS}" | sort > "${TMP_SUMMARY}"

cat > "${SUMMARY_CSV}" <<'CSV'
program,runs,min_mean_seconds,max_mean_seconds,avg_mean_seconds,stddev_seconds,cv_percent,spread_percent
CSV
cat "${TMP_SUMMARY}" >> "${SUMMARY_CSV}"

cat > "${SUMMARY_MD}" <<'MD'
# Program Benchmark Variance Summary

Mean runtime variance across repeated `bench:programs` runs.

| program | runs | min mean (s) | max mean (s) | avg mean (s) | stddev (s) | CV % | spread % |
|---|---:|---:|---:|---:|---:|---:|---:|
MD

awk -F, '{
  printf "| %s | %s | %.9f | %.9f | %.9f | %.9f | %.3f | %.3f |\n",
    $1, $2, $3, $4, $5, $6, $7, $8
}' "${TMP_SUMMARY}" >> "${SUMMARY_MD}"

rm -f "${TMP_ROWS}" "${TMP_SUMMARY}"

echo "Wrote:"
echo "  ${SUMMARY_CSV}"
echo "  ${SUMMARY_MD}"
echo "  ${RUNS_DIR}/"
