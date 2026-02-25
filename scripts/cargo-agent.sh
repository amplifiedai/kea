#!/usr/bin/env bash
set -euo pipefail

# Run cargo with an agent-scoped target dir to avoid cross-agent
# contention on Cargo's `target/.cargo-lock`.
if [ "$#" -lt 1 ]; then
  echo "usage: scripts/cargo-agent.sh <cargo-args...>" >&2
  exit 2
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

is_workspace_scope() {
  for arg in "$@"; do
    case "$arg" in
      --workspace|--all)
        return 0
        ;;
    esac
  done
  return 1
}

has_explicit_target_scope() {
  while [ "$#" -gt 0 ]; do
    case "$1" in
      -p|--package|--manifest-path)
        return 0
        ;;
      --package=*|--manifest-path=*)
        return 0
        ;;
    esac
    shift
  done
  return 1
}

enforce_targeted_tests() {
  if is_workspace_scope "$@"; then
    if [ "${KEA_ALLOW_WORKSPACE_TESTS:-0}" != "1" ]; then
      cat >&2 <<'EOF'
Refusing broad workspace test run without explicit opt-in.
Use one of:
  PKG=<crate> mise run test-pkg
  PKG=<crate> mise run test-pkg-integration
Or rerun with:
  KEA_ALLOW_WORKSPACE_TESTS=1
EOF
      exit 2
    fi
    return 0
  fi

  if has_explicit_target_scope "$@"; then
    return 0
  fi

  cwd="$(pwd -P 2>/dev/null || pwd)"
  if [ "$cwd" = "$ROOT_DIR" ]; then
    cat >&2 <<'EOF'
Refusing unscoped root-level test run.
Pass -p <crate> or --manifest-path <path>, or use a mise test task.
EOF
    exit 2
  fi
}

case "${1:-}" in
  test)
    enforce_targeted_tests "$@"
    ;;
  nextest)
    if [ "${2:-}" = "run" ]; then
      enforce_targeted_tests "$@"
    fi
    ;;
esac

agent_slot="${KEA_AGENT_SLOT:-${AGENT_ID:-${CODEX_AGENT_ID:-${CODEX_THREAD_ID:-}}}}"
if [ -z "${agent_slot:-}" ] && [ -n "${__MISE_SESSION:-}" ]; then
  if command -v shasum >/dev/null 2>&1; then
    agent_slot="mise-$(printf '%s' "$__MISE_SESSION" | shasum | awk '{print substr($1,1,16)}')"
  else
    agent_slot="mise-$(printf '%s' "$__MISE_SESSION" | cksum | awk '{print $1}')"
  fi
fi
if [ -z "${agent_slot:-}" ]; then
  agent_slot="session-${PPID:-$$}"
fi

# Keep slot path-safe and bounded.
agent_slot="$(printf '%s' "$agent_slot" | tr -cs '[:alnum:]._-' '-' | cut -c1-64)"

target_root="${KEA_AGENT_TARGET_ROOT:-/tmp/kea-agent-targets}"
target_dir="${KEA_AGENT_TARGET_DIR:-$target_root/$USER/$agent_slot}"

mkdir -p "$target_dir"
export CARGO_TARGET_DIR="$target_dir"

exec ./scripts/with-rust-cache.sh cargo "$@"
