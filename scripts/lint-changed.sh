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
if printf '%s\n' "$changed_files" | rg -q '^(Cargo\.toml|Cargo\.lock)$'; then
  workspace_fallback=1
fi

if [ "$workspace_fallback" -eq 1 ]; then
  echo "Root manifest/tooling changed; running workspace clippy."
  ./scripts/cargo-agent.sh clippy --workspace --all-targets -- -D warnings
  exit 0
fi

workspace_packages="$(
  printf '%s\n' "$changed_files" \
    | awk -F/ '$1=="crates" {print $2}' \
    | sort -u
)"

ran_any=0

if [ -n "$workspace_packages" ]; then
  pkg_args=()
  while IFS= read -r pkg; do
    [ -n "$pkg" ] || continue
    pkg_args+=("-p" "$pkg")
  done <<< "$workspace_packages"
  echo "Running workspace clippy for changed packages: $workspace_packages"
  ./scripts/cargo-agent.sh clippy "${pkg_args[@]}" --all-targets -- -D warnings
  ran_any=1
fi

if [ "$ran_any" -eq 0 ]; then
  echo "No changed crates detected; skipping clippy."
fi
