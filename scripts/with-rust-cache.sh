#!/usr/bin/env bash
set -euo pipefail

# Opportunistically enable compiler caching when sccache is installed.
if command -v sccache >/dev/null 2>&1; then
  export RUSTC_WRAPPER="$(command -v sccache)"
fi

cpu_count="$(
  sysctl -n hw.logicalcpu 2>/dev/null \
    || getconf _NPROCESSORS_ONLN 2>/dev/null \
    || echo 8
)"

# Keep compile fan-out bounded to avoid runaway memory pressure when multiple
# tools/agents are active on the same machine.
if [ -z "${CARGO_BUILD_JOBS:-}" ]; then
  build_jobs="$cpu_count"
  if [ "$build_jobs" -gt 6 ]; then
    build_jobs=6
  fi
  export CARGO_BUILD_JOBS="$build_jobs"
fi

# Shared default for test harness parallelism (tasks may override).
if [ -z "${KEA_TEST_THREADS:-}" ]; then
  test_threads="$cpu_count"
  if [ "$test_threads" -gt 2 ]; then
    test_threads=2
  fi
  export KEA_TEST_THREADS="$test_threads"
fi

# Serialize cargo invocations across agent shells to prevent lock contention
# and memory blowups from overlapping builds/tests.
if [ "${1:-}" = "cargo" ] && [ "${KEA_CARGO_SERIALIZE:-1}" != "0" ]; then
  pwd_key="$(pwd -P 2>/dev/null || pwd)"
  target_key="${CARGO_TARGET_DIR:-target}"
  lock_key_input="${pwd_key}|${target_key}"
  if command -v shasum >/dev/null 2>&1; then
    lock_key="$(printf '%s' "$lock_key_input" | shasum | awk '{print $1}')"
  else
    lock_key="$(printf '%s' "$lock_key_input" | cksum | awk '{print $1}')"
  fi
  lock_dir="${KEA_CARGO_LOCK_DIR:-/tmp/kea-cargo-serial-${lock_key}.lock}"
  lock_timeout="${KEA_CARGO_LOCK_TIMEOUT_SECS:-1800}"
  lock_stale_secs="${KEA_CARGO_LOCK_STALE_SECS:-7200}"
  lock_start="$(date +%s)"

  lock_mtime() {
    if stat -f '%m' "$1" >/dev/null 2>&1; then
      stat -f '%m' "$1"
    else
      stat -c '%Y' "$1"
    fi
  }

  is_cargo_process() {
    owner_pid="$1"
    owner_cmd="$(ps -p "$owner_pid" -o command= 2>/dev/null || true)"
    case "$owner_cmd" in
      *"/cargo "*|*" cargo "*|*"cargo-nextest "*|*"rustc "*)
        return 0
        ;;
      *)
        return 1
        ;;
    esac
  }

  while ! mkdir "$lock_dir" 2>/dev/null; do
    now="$(date +%s)"
    if [ -f "$lock_dir/pid" ]; then
      owner_pid="$(cat "$lock_dir/pid" 2>/dev/null || true)"
      if [ -n "$owner_pid" ] && ! kill -0 "$owner_pid" 2>/dev/null; then
        rm -rf "$lock_dir"
        continue
      fi
      if [ -n "$owner_pid" ] && ! is_cargo_process "$owner_pid"; then
        rm -rf "$lock_dir"
        continue
      fi
    fi

    if [ -d "$lock_dir" ]; then
      lock_mtime_epoch="$(lock_mtime "$lock_dir" 2>/dev/null || true)"
      if [ -n "${lock_mtime_epoch:-}" ]; then
        lock_age="$((now - lock_mtime_epoch))"
        if [ "$lock_age" -ge "$lock_stale_secs" ]; then
          rm -rf "$lock_dir"
          continue
        fi
      fi
    fi

    waited="$((now - lock_start))"
    if [ "$waited" -ge "$lock_timeout" ]; then
      echo "cargo lock wait timed out after ${lock_timeout}s ($lock_dir)" >&2
      exit 124
    fi

    if [ "$((waited % 30))" -eq 0 ] && [ "$waited" -gt 0 ]; then
      owner_pid="$(cat "$lock_dir/pid" 2>/dev/null || true)"
      owner_cmd="$(ps -p "${owner_pid:-0}" -o command= 2>/dev/null || true)"
      echo "waiting for cargo lock: ${waited}s ($lock_dir, owner_pid=${owner_pid:-unknown}, owner_cmd=${owner_cmd:-unknown})" >&2
    fi
    sleep 1
  done

  printf '%s\n' "$$" > "$lock_dir/pid"
  printf '%s\n' "$(date +%s)" > "$lock_dir/started_at"
  printf '%s\n' "$pwd_key" > "$lock_dir/cwd"
  printf '%s\n' "$*" > "$lock_dir/cmd"
  cleanup_lock() {
    rm -rf "$lock_dir"
  }
  trap cleanup_lock EXIT INT TERM
fi

exec "$@"
