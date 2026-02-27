#!/usr/bin/env bash
set -euo pipefail

SUMMARY_CSV="${1:-benchmark-results/latest/divan.summary.csv}"
OUT_FILE="${2:-benchmark-results/latest/update-fusion.contract.md}"
MAX_DELTA_PCT="${3:-10}"

if [ ! -f "${SUMMARY_CSV}" ]; then
  echo "missing benchmark summary: ${SUMMARY_CSV}" >&2
  exit 2
fi

parse_ns() {
  local v="$1"
  v="$(echo "$v" | tr -d '[:space:]')"
  if [[ "$v" == *"µs" ]]; then
    echo "${v%µs} * 1000" | bc -l
  elif [[ "$v" == *"us" ]]; then
    echo "${v%us} * 1000" | bc -l
  elif [[ "$v" == *"ms" ]]; then
    echo "${v%ms} * 1000000" | bc -l
  elif [[ "$v" == *"ns" ]]; then
    echo "${v%ns}" | bc -l
  elif [[ "$v" == *"s" ]]; then
    echo "${v%s} * 1000000000" | bc -l
  else
    echo "$v" | bc -l
  fi
}

single_median="$(awk -F, '$1=="lower_record_update_single_to_mir"{print $5; exit}' "${SUMMARY_CSV}")"
chain_median="$(awk -F, '$1=="lower_record_update_chain_to_mir"{print $5; exit}' "${SUMMARY_CSV}")"

if [ -z "${single_median}" ] || [ -z "${chain_median}" ]; then
  echo "missing update-fusion benchmark rows in ${SUMMARY_CSV}" >&2
  exit 2
fi

single_ns="$(parse_ns "${single_median}")"
chain_ns="$(parse_ns "${chain_median}")"
delta_pct="$(echo "scale=4; ((${chain_ns} - ${single_ns}) / ${single_ns}) * 100" | bc -l)"

mkdir -p "$(dirname "${OUT_FILE}")"
cat > "${OUT_FILE}" <<EOF
# Update Fusion Contract

- baseline op: \`lower_record_update_single_to_mir\`
- chained op: \`lower_record_update_chain_to_mir\`
- single median: ${single_median}
- chain median: ${chain_median}
- delta: ${delta_pct}% (max allowed: ${MAX_DELTA_PCT}%)
EOF

echo "Wrote ${OUT_FILE}"

if [ "$(echo "${delta_pct} > ${MAX_DELTA_PCT}" | bc -l)" -eq 1 ]; then
  echo "update-fusion contract failed: chained update median regressed by ${delta_pct}% > ${MAX_DELTA_PCT}%" >&2
  exit 1
fi
