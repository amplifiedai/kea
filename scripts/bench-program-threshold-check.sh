#!/usr/bin/env bash
set -euo pipefail

CURRENT_JSON="${1:-benchmark-results/programs/latest/hyperfine.json}"
BASELINES_CSV="${2:-benchmarks/baselines/program-bench-thresholds.csv}"
OUT_DIR="${3:-benchmark-results/programs-regression/latest}"

if [ ! -f "${CURRENT_JSON}" ]; then
  echo "missing current hyperfine json: ${CURRENT_JSON}" >&2
  exit 2
fi
if [ ! -f "${BASELINES_CSV}" ]; then
  echo "missing baseline threshold file: ${BASELINES_CSV}" >&2
  exit 2
fi
if ! command -v jq >/dev/null 2>&1; then
  echo "jq is required for program benchmark threshold checks" >&2
  exit 2
fi

mkdir -p "${OUT_DIR}"
CURRENT_CSV="${OUT_DIR}/current.csv"
SUMMARY_CSV="${OUT_DIR}/regression.summary.csv"
SUMMARY_MD="${OUT_DIR}/regression.summary.md"
FAIL_FILE="${OUT_DIR}/fail.count"

jq -r '.results[] | [.command, (.mean|tostring)] | @csv' "${CURRENT_JSON}" | sed 's/^"//;s/"$//' \
  > "${CURRENT_CSV}"

cat > "${SUMMARY_CSV}" <<'CSV'
program,baseline_mean_seconds,current_mean_seconds,delta_pct,max_regression_pct,status
CSV

awk -F, -v out="${SUMMARY_CSV}" -v failfile="${FAIL_FILE}" '
function trim(s) {
  gsub(/^[ \t"]+/, "", s)
  gsub(/[ \t"]+$/, "", s)
  return s
}

FNR == NR {
  key = trim($1)
  current[key] = trim($2) + 0
  next
}

FNR == 1 { next }

{
  program = trim($1)
  baseline = trim($2) + 0
  threshold = trim($3) + 0

  status = "PASS"
  delta = 0
  current_mean = 0

  if (!(program in current)) {
    status = "MISSING"
    delta = 999999
    failures += 1
  } else {
    current_mean = current[program]
    if (baseline <= 0 || current_mean < 0) {
      status = "INVALID"
      delta = 999999
      failures += 1
    } else {
      delta = ((current_mean - baseline) / baseline) * 100
      if (delta > threshold) {
        status = "FAIL"
        failures += 1
      }
    }
  }

  printf "%s,%.9f,%.9f,%.3f,%.3f,%s\n",
    program, baseline, current_mean, delta, threshold, status >> out
}

END {
  print failures + 0 > failfile
}
' "${CURRENT_CSV}" "${BASELINES_CSV}"

cat > "${SUMMARY_MD}" <<'MD'
# Program Benchmark Regression Summary

Comparison against configured whole-program baseline thresholds.

| program | baseline mean (s) | current mean (s) | delta % | max regression % | status |
|---|---:|---:|---:|---:|---|
MD

awk -F, 'NR > 1 {
  printf "| %s | %.9f | %.9f | %.3f | %.3f | %s |\n", $1, $2, $3, $4, $5, $6
}' "${SUMMARY_CSV}" >> "${SUMMARY_MD}"

FAILURES="$(cat "${FAIL_FILE}")"
rm -f "${FAIL_FILE}" "${CURRENT_CSV}"

echo "Wrote:"
echo "  ${SUMMARY_CSV}"
echo "  ${SUMMARY_MD}"
echo "Failures: ${FAILURES}"

if [ "${FAILURES}" -gt 0 ]; then
  exit 1
fi
