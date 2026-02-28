# Agent Note: 0e Remedy

Read `BRIEFS/in-progress/0e-remedy.md` for the full brief. This note
tells you what to do and in what order.

## Priority

**Item 1 is a correctness bug. Fix it first. Nothing else matters
until multi-operation effects work.**

## Item 1: Handler Cell-Per-Operation

The bug: `active_effect_cells` maps effect name → one cell. All 0-arg
operations in the same effect read from that one cell. An effect with
`a() -> 1` and `b() -> 2` returns 1 for both.

The fix: change the cell map key from effect name to (effect, operation)
pair. Each 0-arg clause initializes its own cell. Each operation reads
its own cell.

Specifically:
1. `active_effect_cells: BTreeMap<String, MirValueId>` →
   `BTreeMap<(String, String), MirValueId>`
2. In `lower_handle_expr` (line ~2810): create a cell per 0-arg clause,
   not one cell for the whole effect. Each clause's resume value
   initializes its own cell.
3. In call lowering (line ~3120): look up
   `active_effect_cells.get(&(effect, operation))` instead of
   `active_effect_cells.get(&effect)`.
4. For `StoreArgAndReturnUnit` (1-arg ops): same change — each 1-arg
   operation stores to its own cell.

Write a test first:
```kea
effect Foo
  fn a() -> Int
  fn b() -> Int

fn body() -> Int -[Foo]>
  Foo.a() + Foo.b()

fn main() -> Int
  handle body() with
    Foo.a() -> resume(10)
    Foo.b() -> resume(2)
-- expected: 12, currently returns: 20
```

Verify JIT and eval paths both return 12.

## Item 3: Real JIT IO Shims

Replace the stubs in `crates/kea-codegen/src/lib.rs:357-380` with
real implementations. Use Rust std::fs, exposed as `extern "C"`:

```rust
unsafe extern "C" fn kea_io_read_file_impl(path: *const c_char) -> *const c_char {
    // CStr from path, fs::read_to_string, leak CString, return ptr
}

unsafe extern "C" fn kea_io_write_file_impl(path: *const c_char, data: *const c_char) -> i8 {
    // CStr both args, fs::write, return 0 on success / -1 on error
}
```

Test: write a temp file via JIT, read it back, verify contents match.

## Item 2: AOT Linking

`kea build` links with `cc` but provides no runtime library for
`__kea_io_*` / `__kea_net_*` symbols. Two options:

- **(a) Emit shims in the object.** Generate the shim function bodies
  as Cranelift IR in the AOT module with `Linkage::Local`. No external
  runtime needed. This is the simpler option.
- **(b) Build a static libkea_rt.a.** Link it in the `cc` invocation.
  More moving parts.

Prefer (a). Test: `kea build` a program with IO, run the binary.

## Item 4: Clock.monotonic

Change `Clock.monotonic` from `time()` to
`clock_gettime(CLOCK_MONOTONIC)`. Import `clock_gettime` instead of
(or in addition to) `time`. Return nanoseconds or (seconds, nanos).
Small, independent fix.

## Item 5: $ Error Message

One-line change at `crates/kea-syntax/src/parser.rs:2754`:
```
- "`$` placeholder expressions are not supported",
+ "`$` placeholder expressions are not yet implemented",
```

## What NOT to fix

- **Item 6 (pop_scope):** The `debug_assert` is correct. Don't add a
  defensive guard — it would hide caller bugs.
- **Items 7-9 (refactors):** Do these opportunistically if you're
  already in those files. Don't seek them out.

## Validation

After items 1-4:
```
mise run check-full
PKG=kea-mir mise run test-pkg
PKG=kea-codegen mise run test-pkg
PKG=kea mise run test-pkg
```

All must pass. The multi-operation effect test is the critical one.
