# Brief: 0e Post-Completion Remedy

**Status:** active
**Priority:** v1-critical
**Depends on:** nothing (all issues are in shipped code)
**Blocks:** 0g (advanced types cannot build on broken effect runtime), stdlib-bootstrap (IO/Net shims must work)

## Context

A post-completion review of 0a-0e found issues in the effect runtime
shipped by 0e. This remedy brief tracks verified fixes.

**Rule: fix Critical items before new feature work on affected crates.**

---

## Critical

### 1. Multi-operation effect handlers share one cell — semantically wrong

**Verified.** The handler lowering model uses one `StateCellNew` per
*effect*, not per *operation*. All 0-arg operations lower to `LoadCell`
(read from the shared cell), initialized from the *first* 0-arg
clause's resume value. All 1-arg operations lower to
`StoreArgAndReturnUnit` (write to the same cell).

This means an effect with two getters returns the same value for both:

```kea
effect Foo
  fn a() -> Int
  fn b() -> Int

handle body() with
  Foo.a() -> resume(1)
  Foo.b() -> resume(2)
-- Foo.a() returns 1 (correct)
-- Foo.b() returns 1 (WRONG — reads same cell, initialized from first clause)
```

The `operation_lowering` map correctly routes each operation name to
its lowering kind (line 2746-2762), but the underlying cell is shared
(line 2810-2820: one `StateCellNew`, stored in `active_effect_cells`
keyed by effect name, not operation name).

**Root cause:** The lowering model assumes State-like (one getter, one
setter) effects. It doesn't generalise to effects with multiple
distinct operations.

**Fix:** Either:
- (a) One cell per operation (each 0-arg clause initializes its own
  cell, each operation reads/writes its own cell), or
- (b) A tagged cell with per-operation slots (one allocation, indexed
  by operation tag).

Option (a) is simpler and correct. The `active_effect_cells` map
changes from `BTreeMap<String, MirValueId>` (effect → cell) to
`BTreeMap<(String, String), MirValueId>` (effect+operation → cell).

**Files:**
- `crates/kea-mir/src/lib.rs:2810-2820` — one cell per effect
- `crates/kea-mir/src/lib.rs:3120` — cell lookup by effect name only
- `crates/kea-mir/src/lib.rs:3151` — LoadCell from shared cell
- `crates/kea-mir/src/lib.rs:3167` — StoreCell to shared cell

**Test:** Effect with 2+ zero-arg operations returning different
values. Verify each returns its own value. Both JIT and eval paths.

---

## High

### 2. AOT build path has no runtime library for IO/Net symbols

**Verified.** `kea build` (line `crates/kea/src/main.rs:183`) links
via `cc` with just the emitted object. The object imports
`__kea_io_read_file`, `__kea_io_write_file`, `__kea_net_connect`,
`__kea_net_send`, `__kea_net_recv` as `Linkage::Import` — but no
runtime library provides them. Any program using IO/Net fails to link.

JIT works because `register_jit_runtime_symbols` (line 382) maps
these symbols to in-process stubs. AOT has no equivalent.

**Fix:** Emit the runtime shims as Cranelift-generated functions
directly in the object module (use `Linkage::Local` instead of
`Linkage::Import`). This makes AOT binaries self-contained without
needing a separate runtime library. The shims are small wrappers
around libc.

**Files:**
- `crates/kea-codegen/src/lib.rs:643-767` — Import declarations
- `crates/kea/src/main.rs:183` — link step

**Test:** `kea build` a program using `IO.write_file` + `IO.read_file`.
Run the resulting binary. Verify it works.

---

### 3. JIT IO/Net shims are placeholders, not real implementations

**Verified.** The stub implementations at `crates/kea-codegen/src/lib.rs:357-380`:
- `kea_io_read_file_stub`: returns the input path pointer (not file contents)
- `kea_io_write_file_stub`: returns 0, does nothing
- `kea_net_connect_stub`: returns 1 regardless
- `kea_net_send_stub`: returns 0, does nothing
- `kea_net_recv_stub`: returns size argument

These are clearly scaffolding from 0e implementation, but the brief
was moved to done/ without documenting them as known limitations.

**Fix:** Implement real shims using Rust `std::fs` and `std::net`,
exposed as `extern "C"` functions. Doesn't need to be async or
buffered — just correct (read_file reads, write_file writes).

**Test:** JIT test: write file, read it back, verify contents match.

---

### 4. Clock.monotonic uses wall-clock `time()`, not monotonic clock

**Verified.** Line 497: `("Clock", "now" | "monotonic")` maps both
operations to the same `requires_clock_time` flag, which imports
`time()` (wall-clock seconds, 1-second granularity). Monotonic should
use `clock_gettime(CLOCK_MONOTONIC)` for nanosecond resolution and
monotonic guarantees.

**Fix:** Import `clock_gettime` and call with `CLOCK_MONOTONIC` for
monotonic, `CLOCK_REALTIME` for now.

**Test:** Two consecutive `Clock.monotonic` calls; second >= first.
Verify sub-second granularity.

---

## Medium

### 5. `$` placeholder syntax explicitly rejected

**Verified.** Line 2749-2758: parser recognizes `$` but emits a
"not supported" error. This is documented Kea syntax (KERNEL, CLAUDE.md)
for receiver placement (`xs.map($ + 1)`).

**Assessment:** This is a feature implementation, not a bug. `$` was
likely intentionally deferred. However, the error message should say
"not yet implemented" rather than "not supported" — the current
wording implies it's a deliberate design exclusion.

**Fix (minimal):** Change error message to "$ placeholder expressions
are not yet implemented". Track full `$` implementation as a feature
item (check if any brief covers it; if not, add to 0g or create a
separate brief).

---

### 6. TypeEnv::pop_scope can underflow

**Partially verified.** `pop_scope` (line 867) does `self.bindings.pop()`
with a `debug_assert` guard — so in debug builds it panics with a
clear message, in release builds it silently empties the Vec. A
subsequent `bind` (line 858) would `unwrap()` on an empty Vec.

**Assessment:** The `debug_assert` is the right guard for a correctness
invariant — this should never happen. The review agent calls it a
"panic footgun" but a debug_assert that fires means a caller bug, not
a missing guard. Adding a defensive `len() > 1` check would *hide*
the caller bug, which is worse.

**Fix:** No code change needed. The `debug_assert` is correct.
*If* this ever fires, fix the caller that over-pops, don't silence
the assert.

---

## Refactor (non-blocking)

### 7. Monolithic CLI test suite in main.rs

The review agent reports thousands of lines of tests in
`crates/kea/src/main.rs`. Worth splitting into `tests/` modules when
convenient, but not blocking.

### 8. Test runner recompiles per iteration

`crates/kea/src/compiler.rs:240` — property/multi-run tests recompile
each iteration. Compile-once + execute-many would be faster. Do when
touching test infrastructure.

### 9. Duplicate HIR lowering in compile/execute paths

`emit_object` and `execute_jit` both call `lower_module` independently.
Cache in `CompilationContext`. Do when refactoring the compiler module.

---

## Execution Order

1. **Item 1** (handler correctness) — multi-operation effects are
   semantically wrong. Fix first.
2. **Item 3** (JIT shims) — make IO shims real so tests can validate
   item 2 with real IO.
3. **Item 2** (AOT link) — unblocks `kea build` for IO/Net programs.
4. **Item 4** (Clock) — small, independent.
5. **Item 5** ($ message) — one-line string change.
6. **Items 7-9** — opportunistic.

## Validation

After Critical and High items:
- `mise run check-full` passes
- Multi-operation effect test passes (JIT + eval)
- `kea build` + run works for IO program
- JIT `IO.read_file`/`IO.write_file` work correctly
- `Clock.monotonic` has sub-second granularity
- No regressions in existing test suite

## Progress
- 2026-02-28 16:11: Critical item 1 fixed in MIR lowering: handler cells are no longer globally shared by effect label. Dispatch metadata and hidden handler parameters are now operation-scoped (`Effect.operation`), handler lowering allocates per-operation cells for read-only multi-op effects, and keeps shared-cell semantics for stateful read/write effects. Added regression `compile_and_execute_generic_two_getter_tail_handler_exit_code` (Foo.a/Foo.b returns 12) and revalidated existing state/log/reader handler tests. Validation run: `mise run check`, `PKG=kea-mir mise run test-pkg`, `PKG=kea mise run test-pkg`.
- 2026-02-28 16:18: High item 3 completed in `kea-codegen`: JIT runtime shims for capability effects now perform real host behavior instead of placeholders (`IO.write_file`/`IO.read_file` via `std::fs`, `Net.connect/send/recv` via `TcpStream` with a process-local connection table). Updated CLI regressions to validate real file/network behavior without relying on stub artifacts. Validation run: `mise run check`, `PKG=kea-codegen mise run test-pkg`, `PKG=kea mise run test-pkg`.
- **Next:** item 2 (AOT self-contained runtime symbols), then item 4 (clock precision via host clock shim).
