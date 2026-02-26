#!/usr/bin/env bash
set -euo pipefail

RUNS="${1:-3}"
OUT_DIR="${2:-benchmark-results/variance}"

if ! [[ "${RUNS}" =~ ^[0-9]+$ ]] || [ "${RUNS}" -lt 2 ]; then
  echo "usage: $0 <runs>=3 <out-dir>=benchmark-results/variance"
  echo "runs must be an integer >= 2"
  exit 2
fi

RUNS_DIR="${OUT_DIR}/runs"
SUMMARY_CSV="${OUT_DIR}/variance.summary.csv"
SUMMARY_MD="${OUT_DIR}/variance.summary.md"
TMP_CSV="${OUT_DIR}/variance.tmp.csv"

mkdir -p "${RUNS_DIR}"
rm -f "${TMP_CSV}"

echo "Running ${RUNS} benchmark repetitions for variance characterization..."
for idx in $(seq 1 "${RUNS}"); do
  run_dir="${RUNS_DIR}/run-${idx}"
  echo "  run ${idx}/${RUNS}: ${run_dir}"
  ./scripts/bench-export.sh "${run_dir}"
done

awk -F, '
function to_ns(v) {
  gsub(/[[:space:]]+/, "", v)
  gsub(/,/, "", v)
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

FNR == 1 { next }
{
  key = $1 "," $2
  x = to_ns($5)
  count[key] += 1
  sum[key] += x
  sumsq[key] += x * x
  if (!(key in min) || x < min[key]) min[key] = x
  if (!(key in max) || x > max[key]) max[key] = x
}
END {
  for (key in count) {
    n = count[key]
    mean = sum[key] / n
    variance = (sumsq[key] / n) - (mean * mean)
    if (variance < 0) variance = 0
    stddev = sqrt(variance)
    cv = (mean == 0) ? 0 : (stddev / mean) * 100
    spread = (mean == 0) ? 0 : ((max[key] - min[key]) / mean) * 100
    printf "%s,%d,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f\n",
      key, n, min[key], max[key], mean, stddev, cv, spread
  }
}
' "${RUNS_DIR}"/run-*/divan.summary.csv | sort > "${TMP_CSV}"

cat > "${SUMMARY_CSV}" <<'CSV'
benchmark,arg,runs,min_median_ns,max_median_ns,mean_median_ns,stddev_median_ns,cv_percent,spread_percent
CSV
cat "${TMP_CSV}" >> "${SUMMARY_CSV}"

cat > "${SUMMARY_MD}" <<'MD'
# Benchmark Variance Summary

Median timing variance across repeated `bench-export` runs.

| benchmark | arg | runs | min (ns) | max (ns) | mean (ns) | stddev (ns) | CV % | spread % |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
MD

awk -F, '{
  printf "| %s | %s | %s | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f |\n",
    $1, $2, $3, $4, $5, $6, $7, $8, $9
}' "${TMP_CSV}" >> "${SUMMARY_MD}"

rm -f "${TMP_CSV}"

echo "Wrote:"
echo "  ${SUMMARY_CSV}"
echo "  ${SUMMARY_MD}"
echo "  ${RUNS_DIR}/"
