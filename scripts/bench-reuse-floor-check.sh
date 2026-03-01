#!/usr/bin/env bash
set -euo pipefail

CURRENT_JSON="${1:-benchmark-results/latest/reuse.metrics.json}"
BASELINES_CSV="${2:-benchmarks/baselines/reuse-token-floors.csv}"
OUT_DIR="${3:-benchmark-results/regression/latest}"

if [ ! -f "${CURRENT_JSON}" ]; then
  echo "missing reuse metrics json: ${CURRENT_JSON}" >&2
  exit 2
fi
if [ ! -f "${BASELINES_CSV}" ]; then
  echo "missing reuse-token floor file: ${BASELINES_CSV}" >&2
  exit 2
fi
if ! command -v jq >/dev/null 2>&1; then
  echo "jq is required for reuse-token floor checks" >&2
  exit 2
fi

mkdir -p "${OUT_DIR}"
SUMMARY_CSV="${OUT_DIR}/reuse.regression.summary.csv"
SUMMARY_MD="${OUT_DIR}/reuse.regression.summary.md"

cat > "${SUMMARY_CSV}" <<'CSV'
scope,consumed,min_consumed,coverage_pct,min_coverage_pct,trmc_candidates,max_trmc_candidates,status
CSV

while IFS=, read -r raw_scope raw_min_consumed raw_min_coverage raw_max_trmc; do
  scope="$(echo "${raw_scope}" | tr -d '[:space:]')"
  min_consumed="$(echo "${raw_min_consumed}" | tr -d '[:space:]')"
  min_coverage="$(echo "${raw_min_coverage}" | tr -d '[:space:]')"
  max_trmc="$(echo "${raw_max_trmc:-}" | tr -d '[:space:]')"
  if [ -z "${scope}" ] || [ "${scope#\#}" != "${scope}" ] || [ "${scope}" = "scope" ]; then
    continue
  fi

  if [ "${scope}" = "totals" ]; then
    consumed="$(jq -r '.totals.reuse_token_consumed_count // 0' "${CURRENT_JSON}")"
    coverage="$(jq -r '.totals.reuse_token_coverage_pct // 0' "${CURRENT_JSON}")"
    trmc_candidates="$(jq -r '.totals.trmc_candidate_count // 0' "${CURRENT_JSON}")"
  else
    consumed="$(jq -r --arg name "${scope}" '.kernels[] | select(.name == $name) | .reuse_token_consumed_count' "${CURRENT_JSON}")"
    coverage="$(jq -r --arg name "${scope}" '.kernels[] | select(.name == $name) | .reuse_token_coverage_pct' "${CURRENT_JSON}")"
    trmc_candidates="$(jq -r --arg name "${scope}" '.kernels[] | select(.name == $name) | .trmc_candidate_count' "${CURRENT_JSON}")"
    if [ -z "${consumed}" ] || [ -z "${coverage}" ]; then
      echo "scope `${scope}` missing from ${CURRENT_JSON}" >&2
      consumed=0
      coverage=0
      trmc_candidates=0
      status="MISSING"
      printf "%s,%s,%s,%s,%s,%s,%s,%s\n" \
        "${scope}" "${consumed}" "${min_consumed}" "${coverage}" "${min_coverage}" "${trmc_candidates}" "${max_trmc}" "${status}" >> "${SUMMARY_CSV}"
      continue
    fi
  fi

  status="PASS"
  if [ "${consumed}" -lt "${min_consumed}" ]; then
    status="FAIL"
  fi
  if awk "BEGIN { exit !(${coverage} < ${min_coverage}) }"; then
    status="FAIL"
  fi
  if [ -n "${max_trmc}" ] && awk "BEGIN { exit !(${trmc_candidates} > ${max_trmc}) }"; then
    status="FAIL"
  fi

  printf "%s,%s,%s,%s,%s,%s,%s,%s\n" \
    "${scope}" "${consumed}" "${min_consumed}" "${coverage}" "${min_coverage}" "${trmc_candidates}" "${max_trmc}" "${status}" >> "${SUMMARY_CSV}"
done < "${BASELINES_CSV}"

cat > "${SUMMARY_MD}" <<'MD'
# Reuse Token Conversion Floor

| scope | consumed | min consumed | coverage % | min coverage % | trmc candidates | max trmc candidates | status |
|---|---:|---:|---:|---:|---:|---:|---|
MD

awk -F, 'NR > 1 {
  max_trmc = ($7 == "" ? "-" : $7)
  printf "| %s | %s | %s | %.3f | %.3f | %s | %s | %s |\n", $1, $2, $3, $4, $5, $6, max_trmc, $8
}' "${SUMMARY_CSV}" >> "${SUMMARY_MD}"

FAILURES="$(awk -F, 'NR > 1 && $8 != "PASS" { c += 1 } END { print c + 0 }' "${SUMMARY_CSV}")"

echo "Wrote:"
echo "  ${SUMMARY_CSV}"
echo "  ${SUMMARY_MD}"
echo "Failures: ${FAILURES}"

if [ "${FAILURES}" -gt 0 ]; then
  exit 1
fi
