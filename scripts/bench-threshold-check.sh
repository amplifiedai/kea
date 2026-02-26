#!/usr/bin/env bash
set -euo pipefail

CURRENT_CSV="${1:-benchmark-results/latest/divan.summary.csv}"
BASELINES_CSV="${2:-benchmarks/baselines/microbench-thresholds.csv}"
OUT_DIR="${3:-benchmark-results/regression/latest}"

if [ ! -f "${CURRENT_CSV}" ]; then
  echo "missing current benchmark summary: ${CURRENT_CSV}" >&2
  exit 2
fi
if [ ! -f "${BASELINES_CSV}" ]; then
  echo "missing baseline threshold file: ${BASELINES_CSV}" >&2
  exit 2
fi

mkdir -p "${OUT_DIR}"
SUMMARY_CSV="${OUT_DIR}/regression.summary.csv"
SUMMARY_MD="${OUT_DIR}/regression.summary.md"
FAIL_FILE="${OUT_DIR}/fail.count"

cat > "${SUMMARY_CSV}" <<'CSV'
benchmark,arg,baseline_median,current_median,delta_pct,max_regression_pct,status
CSV

awk -F, -v out="${SUMMARY_CSV}" -v failfile="${FAIL_FILE}" '
function trim(s) {
  gsub(/^[ \t]+/, "", s)
  gsub(/[ \t]+$/, "", s)
  return s
}

function to_ns(v) {
  v = trim(v)
  if (v ~ /µs$/) {
    sub(/µs$/, "", v)
    return (v + 0) * 1000
  }
  if (v ~ /us$/) {
    sub(/us$/, "", v)
    return (v + 0) * 1000
  }
  if (v ~ /ms$/) {
    sub(/ms$/, "", v)
    return (v + 0) * 1000000
  }
  if (v ~ /ns$/) {
    sub(/ns$/, "", v)
    return v + 0
  }
  if (v ~ /s$/) {
    sub(/s$/, "", v)
    return (v + 0) * 1000000000
  }
  return v + 0
}

FNR == NR {
  if (FNR == 1) next
  key = trim($1) "," trim($2)
  current[key] = trim($5)
  next
}

FNR == 1 { next }

{
  bench = trim($1)
  arg = trim($2)
  baseline = trim($3)
  threshold = trim($4) + 0
  key = bench "," arg

  status = "PASS"
  delta = 0
  current_median = ""

  if (!(key in current)) {
    status = "MISSING"
    delta = 999999
    failures += 1
  } else {
    current_median = current[key]
    baseline_ns = to_ns(baseline)
    current_ns = to_ns(current_median)
    if (baseline_ns <= 0 || current_ns < 0) {
      status = "INVALID"
      delta = 999999
      failures += 1
    } else {
      delta = ((current_ns - baseline_ns) / baseline_ns) * 100
      if (delta > threshold) {
        status = "FAIL"
        failures += 1
      }
    }
  }

  printf "%s,%s,%s,%s,%.3f,%.3f,%s\n",
    bench, arg, baseline, current_median, delta, threshold, status >> out
}

END {
  print failures + 0 > failfile
}
' "${CURRENT_CSV}" "${BASELINES_CSV}"

cat > "${SUMMARY_MD}" <<'MD'
# Benchmark Regression Summary

Comparison against configured baseline thresholds.

| benchmark | arg | baseline | current | delta % | max regression % | status |
|---|---:|---:|---:|---:|---:|---|
MD

awk -F, 'NR > 1 {
  printf "| %s | %s | %s | %s | %.3f | %.3f | %s |\n", $1, $2, $3, $4, $5, $6, $7
}' "${SUMMARY_CSV}" >> "${SUMMARY_MD}"

FAILURES="$(cat "${FAIL_FILE}")"
rm -f "${FAIL_FILE}"

echo "Wrote:"
echo "  ${SUMMARY_CSV}"
echo "  ${SUMMARY_MD}"
echo "Failures: ${FAILURES}"

if [ "${FAILURES}" -gt 0 ]; then
  exit 1
fi
