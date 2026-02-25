#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

changed_files="$(
  {
    git diff --name-only HEAD --
    git ls-files --others --exclude-standard
  } | sort -u
)"

workspace_fallback=0
if printf '%s\n' "$changed_files" | rg -q '^(Cargo\.toml|Cargo\.lock|mise\.toml|scripts/)'; then
  workspace_fallback=1
fi

if [ "$workspace_fallback" -eq 1 ]; then
  echo "Root manifest/tooling changed; running workspace fast tests."
  if ./scripts/cargo-agent.sh nextest --version >/dev/null 2>&1; then
    KEA_ALLOW_WORKSPACE_TESTS=1 ./scripts/cargo-agent.sh nextest run --profile fast --workspace --lib --bins
  else
    THREADS="${KEA_TEST_THREADS_FAST:-2}"
    KEA_ALLOW_WORKSPACE_TESTS=1 ./scripts/cargo-agent.sh test --workspace --lib --bins -- --test-threads "${THREADS}"
  fi
  exit 0
fi

workspace_packages="$(
  printf '%s\n' "$changed_files" \
    | awk -F/ '$1=="crates" {print $2}' \
    | sort -u
)"

ran_any=0

if [ -n "$workspace_packages" ]; then
  while IFS= read -r pkg; do
    [ -n "$pkg" ] || continue
    if ./scripts/cargo-agent.sh nextest --version >/dev/null 2>&1; then
      echo "Running changed-crate tests via nextest: $pkg"
      ./scripts/cargo-agent.sh nextest run --profile fast -p "$pkg" --lib --tests --bins
    else
      THREADS="${KEA_TEST_THREADS_FAST:-2}"
      echo "Running changed-crate tests via cargo test: $pkg"
      ./scripts/cargo-agent.sh test -p "$pkg" --lib --tests --bins -- --test-threads "${THREADS}"
    fi
    ran_any=1
  done <<< "$workspace_packages"
fi

if [ "$ran_any" -eq 0 ]; then
  echo "No changed crates with tests detected; skipping tests."
fi
