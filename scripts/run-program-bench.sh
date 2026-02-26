#!/usr/bin/env bash
set -euo pipefail

KEA_BIN="${1:-}"
PROGRAM="${2:-}"
ITERS="${3:-1}"

if [ -z "${KEA_BIN}" ] || [ -z "${PROGRAM}" ]; then
  echo "usage: $0 <kea-bin> <program.kea> [iters]" >&2
  exit 2
fi

if ! [[ "${ITERS}" =~ ^[0-9]+$ ]] || [ "${ITERS}" -lt 1 ]; then
  echo "iters must be an integer >= 1" >&2
  exit 2
fi

for _ in $(seq 1 "${ITERS}"); do
  "${KEA_BIN}" run "${PROGRAM}" >/dev/null
done
