#!/usr/bin/env bash
set -euo pipefail

OUT_DIR="${1:-benchmark-results/latest}"
mkdir -p "${OUT_DIR}"

RAW_OUT="${OUT_DIR}/divan.raw.txt"
CSV_OUT="${OUT_DIR}/divan.summary.csv"
JSON_OUT="${OUT_DIR}/divan.summary.json"
META_OUT="${OUT_DIR}/meta.json"
TMP_ROWS="${OUT_DIR}/rows.tmp.csv"

echo "Running benchmark harness..."
echo "Output directory: ${OUT_DIR}"

./scripts/cargo-agent.sh bench -p kea-bench --bench core | tee "${RAW_OUT}"

cat > "${CSV_OUT}" <<'CSV'
benchmark,arg,fastest,slowest,median,mean,samples,iters
CSV

awk '
function trim(s) {
  gsub(/^[ \t]+/, "", s)
  gsub(/[ \t]+$/, "", s)
  return s
}
{
  pos = index($0, "├─")
  if (pos == 0) {
    pos = index($0, "╰─")
  }
  if (pos == 0) {
    next
  }

  line = substr($0, pos + 3)
  split(line, parts, "│")
  head = trim(parts[1])

  if (head ~ /^[0-9]+[ \t]+/) {
    if (bench == "") {
      next
    }
    arg = head
    sub(/[ \t].*$/, "", arg)
    fastest = head
    sub(/^[0-9]+[ \t]+/, "", fastest)
    fastest = trim(fastest)
    slowest = trim(parts[2])
    median = trim(parts[3])
    mean = trim(parts[4])
    samples = trim(parts[5])
    iters = trim(parts[6])
    printf "%s,%s,%s,%s,%s,%s,%s,%s\n", bench, arg, fastest, slowest, median, mean, samples, iters
  } else {
    bench = head
  }
}
' "${RAW_OUT}" > "${TMP_ROWS}"

cat "${TMP_ROWS}" >> "${CSV_OUT}"

{
  echo "["
  awk -F, '
    BEGIN { first = 1 }
    {
      if (!first) {
        print ","
      }
      first = 0
      printf "  {\"benchmark\":\"%s\",\"arg\":\"%s\",\"fastest\":\"%s\",\"slowest\":\"%s\",\"median\":\"%s\",\"mean\":\"%s\",\"samples\":\"%s\",\"iters\":\"%s\"}",
        $1, $2, $3, $4, $5, $6, $7, $8
    }
  ' "${TMP_ROWS}"
  echo
  echo "]"
} > "${JSON_OUT}"

GIT_SHA="$(git rev-parse --short HEAD)"
DATE_UTC="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
UNAME_STR="$(uname -a | tr '"' "'")"
RUSTC_VER="$(rustc -V | tr '"' "'")"
HOSTNAME_STR="$(hostname | tr '"' "'")"
SAMPLE_COUNT="${DIVAN_SAMPLE_COUNT:-default}"
SAMPLE_SIZE="${DIVAN_SAMPLE_SIZE:-default}"
MIN_TIME="${DIVAN_MIN_TIME:-default}"
MAX_TIME="${DIVAN_MAX_TIME:-default}"

cat > "${META_OUT}" <<EOF
{
  "git_sha": "${GIT_SHA}",
  "timestamp_utc": "${DATE_UTC}",
  "hostname": "${HOSTNAME_STR}",
  "uname": "${UNAME_STR}",
  "rustc": "${RUSTC_VER}",
  "divan_sample_count": "${SAMPLE_COUNT}",
  "divan_sample_size": "${SAMPLE_SIZE}",
  "divan_min_time": "${MIN_TIME}",
  "divan_max_time": "${MAX_TIME}"
}
EOF

rm -f "${TMP_ROWS}"

echo "Wrote:"
echo "  ${RAW_OUT}"
echo "  ${CSV_OUT}"
echo "  ${JSON_OUT}"
echo "  ${META_OUT}"
