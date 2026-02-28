# Brief: Phase 1a — Foreign Function Interface

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0d (codegen), 0f (Ptr T, unsafe, layout intrinsics), 0g (all Phase 0 complete)
**Blocks:** phase-1b (compiler in Kea needs Cranelift bindings), ecosystem (every C library integration)
**Also read:**
- [KERNEL §17](../../docs/spec/KERNEL.md) — FFI specification
- [Packaging, FFI, comptime](../design/packaging-ffi-comptime.md) — design-level FFI discussion
- [0f-memory-model](../in-progress/0f-memory-model.md) — Ptr T and unsafe implementation

## Motivation

FFI is a language feature, not plumbing. It's how Kea talks to the
outside world — C libraries, system APIs, Cranelift for code
generation. Getting it right means:

- Safe wrappers are natural to write (not painful boilerplate)
- Effect tracking extends across the FFI boundary
- Unique/borrow semantics interact correctly with C ownership
- The idiom of "unsafe inside, safe+effectful outside" is obvious
- The Cranelift bindings (self-hosting's critical dependency) are
  clean and maintainable

This is also the first feature where Kea's effect system meets raw
systems programming. The design here sets the pattern for every
future FFI library: SQLite, OpenSSL, Arrow, system calls.

## Syntax

### External Function Declarations

KERNEL §17.1 specifies `@extern("c")` annotation syntax:

```kea
@extern("c")
fn write(fd: Int32, buf: Ptr UInt8, count: UInt64) -[IO]> Int64

@extern("c")
fn sqlite3_open(filename: Ptr UInt8, db: Ptr (Ptr Sqlite3)) -> CInt
```

Design decisions on the annotation:

- **`@extern("c")` not `extern "C"`.** Kea uses annotations for
  metadata. This is consistent with `@unsafe`, `@with`, `@derive`.
  Rust's `extern "C"` is a keyword-level construct; Kea's is an
  annotation on a normal `fn` declaration.
- **Calling convention is the string parameter.** `"c"` for C ABI,
  `"rust"` for Rust ABI. Extensible to `"win64"`, `"aapcs"`, etc.
  Maps directly to Cranelift's calling convention support.
- **No function body.** `@extern` functions have a signature only.
  The body is provided by the linked native library.

### IO Effect Requirement

KERNEL §17.1: "FFI functions always have at least the `IO` effect.
The compiler cannot verify the purity or safety of foreign code."

This is a hard rule. Even a pure C function like `abs()` gets IO
because the compiler can't prove it's pure. The safe Kea wrapper
can drop IO if the wrapped operation is demonstrably pure:

```kea
@extern("c")
fn c_abs(n: CInt) -[IO]> CInt

struct Int
  --| Return the absolute value.
  fn abs(n: Int) -> Int
    -- We know c_abs is pure, so we handle IO at the wrapper level
    -- Actually, Int.abs should be a Kea intrinsic, not FFI.
    -- This example illustrates the pattern.
    ...
```

**Open question:** Should there be an `@extern("c", pure)` escape
hatch for C functions the programmer guarantees are pure? This
avoids wrapping overhead for pure math libraries. Risk: the
programmer can lie. Proposal: defer. The wrapper pattern is
sufficient for Phase 1. If the overhead matters, add `pure` later
with a lint warning.

### Unsafe Blocks and @unsafe Functions

KERNEL §17.2-17.3 specify the unsafe boundary:

```kea
--| Open a SQLite database, returning a safe handle.
fn open(path: String) -[IO, Fail SqliteError]> Sqlite
  let db = unsafe Ptr.null()
  let rc = unsafe sqlite3_open(path.as_c_str(), Ptr.addr_of(db))
  if rc != 0
    fail SqliteError.from_code(rc)
  Sqlite { handle: db }
```

```kea
@unsafe
fn read_u32_at(ptr: Ptr UInt8, offset: Int) -> UInt32
  let target = ptr.offset(offset)
  Ptr.read(target.cast())
```

Rules:
- `unsafe { expr }` is an expression. The contained expression may
  call `@unsafe` functions and use `Ptr` operations.
- `@unsafe` functions may use unsafe primitives in their body without
  `unsafe` blocks (the annotation covers the entire function).
- Calling an `@unsafe` function from safe code requires an `unsafe`
  block.
- `Ptr T` values may be held in safe code (opaque handles) but only
  dereferenced/offset/cast in unsafe context.
- `Ptr.is_null` is the only safe `Ptr` operation.

### Ptr T Operations

Per KERNEL §17.3:

| Operation | Signature | Description |
|---|---|---|
| `Ptr.read` | `(p: Ptr T) -> T` | Dereference |
| `Ptr.write` | `(p: Ptr T, val: T) -> Unit` | Write value |
| `Ptr.offset` | `(p: Ptr T, n: Int) -> Ptr T` | Advance by n * size_of(T) |
| `Ptr.cast` | `(p: Ptr A) -> Ptr B` | Reinterpret pointer type |
| `Ptr.null` | `() -> Ptr T` | Null pointer |
| `Ptr.is_null` | `(p: Ptr T) -> Bool` | Null check (**safe**) |
| `Ptr.alloc` | `(count: Int) -> Ptr T` | Allocate raw memory |
| `Ptr.free` | `(p: Ptr T) -> Unit` | Free raw memory |

All except `Ptr.is_null` require unsafe context.

### Type Marshalling

Per KERNEL §17.1:

| Kea type | C ABI |
|---|---|
| `Int8..64` | `int8_t..int64_t` |
| `UInt8..64` | `uint8_t..uint64_t` |
| `Float` | `double` |
| `Float32` | `float` |
| `Bool` | `_Bool` / `uint8_t` |
| `Ptr T` | `T*` |
| `Unit` | `void` (return only) |

Managed types (`String`, `List`, `Bytes`) cannot cross FFI directly.
Convert to `Ptr UInt8` + length at the boundary.

### C Type Aliases

Provide type aliases for C portability:

```kea
type CInt = Int32
type CUInt = UInt32
type CLong = Int64       -- on LP64 (Linux/macOS)
type CSize = UInt64      -- on 64-bit
type CChar = UInt8
```

These live in a `ffi.kea` stdlib module and match the target
platform's C ABI. The compiler provides the correct definitions
based on the target triple.

## Implementation

### Step 1: Parser — `@extern` and `unsafe`

Add to the parser:

- **`@extern("c")` annotation** on `fn` declarations. Parse the
  calling convention string. Reject function bodies on extern fns.
- **`unsafe` expression.** `unsafe <expr>` parses as a prefix
  expression. Lowers to `HirUnsafe { body: HirExpr }`.
- **`@unsafe` annotation** on `fn` declarations. Marks the function
  as requiring unsafe context to call.

AST nodes:
```rust
// In kea-ast
ExternFn {
    name: String,
    convention: String,  // "c", "rust", etc.
    params: Vec<Param>,
    return_type: Type,
    effects: EffectRow,
}

UnsafeExpr {
    body: Box<Expr>,
}

// @unsafe is an attribute on FnDecl, not a separate node
```

### Step 2: Type Checker — Effect and Safety Tracking

- **Extern fns must declare IO.** If an `@extern` function's effect
  row doesn't include IO, emit a compile error.
- **Unsafe context tracking.** Track whether we're inside an `unsafe`
  block or `@unsafe` function. Calls to `@unsafe` functions and `Ptr`
  operations outside unsafe context are type errors.
- **Ptr T typing.** `Ptr T` is a primitive type. All operations
  except `is_null` require unsafe context. `Ptr T` is not
  refcounted — it has no Drop, no Unique interaction.

### Step 3: Codegen — C Calling Convention

- **Extern fn calls.** Emit Cranelift `call` instructions using the
  C calling convention. Cranelift has direct support for this via
  `CallConv::SystemV` (Linux/macOS) or `CallConv::WindowsFastcall`.
- **Type lowering.** Map Kea FFI types to Cranelift types:
  `Int32` → `types::I32`, `Ptr T` → `types::I64` (on 64-bit), etc.
- **No RC on Ptr.** `Ptr T` values are raw integers to Cranelift.
  No retain/release, no CoW. The programmer manages lifetime.
- **String marshalling helpers.** `String.as_c_str` copies to a
  null-terminated C string (allocates). `String.from_c_str` copies
  from a null-terminated C string. Both are intrinsics.

### Step 4: Linker Integration — Static Linking

- **`@link("name")` annotation** on extern fns or at module level
  to specify the library to link against.
  ```kea
  @link("sqlite3")
  @extern("c")
  fn sqlite3_open(filename: Ptr UInt8, db: Ptr (Ptr Sqlite3)) -[IO]> CInt
  ```
- **Static linking by default.** `kea build` passes `-lsqlite3` to
  the linker. Dynamic linking opt-in via `@link("sqlite3", dynamic)`.
- **AOT binary includes linked libraries.** The output is a
  self-contained native binary. No runtime library dependencies
  beyond libc.
- **Library search paths.** `KEA_LIB_PATH` environment variable,
  plus system defaults (`/usr/lib`, `/usr/local/lib`). Future:
  `kea.toml` `[native]` section.

### Step 5: Cranelift Bindings Library

Write `cranelift.kea` — the safe Kea wrapper around Cranelift's
C API. This is both a validation of the FFI system and a critical
dependency for Phase 1b.

Cranelift exposes a C API via `cranelift-c-api` crate. The Kea
bindings wrap it with effects:

```kea
struct Cranelift

  --| A Cranelift compilation module.
  --| Use `Cranelift.with_module` to create one.
  type Module = Opaque    -- opaque C handle

  --| Create a new compilation module, execute `f` with it,
  --| and clean up resources when `f` completes.
  fn with_module(f: (Module) -[e]> A) -[IO, Fail CraneliftError, e]> A
    let module = unsafe cranelift_module_new()
    let result = f(module)
    unsafe cranelift_module_free(module)
    result

  --| Define a function in the module.
  fn define_function(
    module: Module,
    name: String,
    params: List CraneliftType,
    returns: List CraneliftType,
    body: (FunctionBuilder) -[IO]> Unit,
  ) -[IO, Fail CraneliftError]> FuncId
    -- ...

  --| Finalize the module and emit machine code.
  fn emit(module: Module) -[IO, Fail CraneliftError]> Bytes
    -- ...
```

The pattern: unsafe C calls inside, safe effectful API outside.
Every C pointer is wrapped in an opaque Kea type. Every fallible
operation uses `Fail CraneliftError`. IO is tracked.

### Step 6: String and Bytes Interop

FFI requires converting between Kea's managed `String`/`Bytes`
and raw `Ptr UInt8`:

```kea
struct String
  --| Convert to a null-terminated C string.
  --| The returned pointer is valid until the String is dropped.
  @unsafe
  fn as_c_str(s: String) -> Ptr UInt8

  --| Create a String from a null-terminated C string.
  --| Copies the data into a Kea-managed String.
  fn from_c_str(ptr: Ptr UInt8) -[IO]> String

struct Bytes
  --| Get a raw pointer to the byte data.
  @unsafe
  fn as_ptr(b: Bytes) -> Ptr UInt8

  --| Get the length in bytes.
  fn length(b: Bytes) -> Int

  --| Create Bytes from a raw pointer and length.
  --| Copies the data into Kea-managed memory.
  fn from_raw(ptr: Ptr UInt8, len: Int) -[IO]> Bytes
```

**Lifetime concern:** `as_c_str` returns a pointer into the
String's internal buffer. If the String is dropped, the pointer
dangles. This is why `as_c_str` is `@unsafe`. The safe pattern is
to use it within a single expression:

```kea
let rc = unsafe sqlite3_open(path.as_c_str(), db_ptr)
```

The compiler should warn (lint, not error) if `as_c_str` result
is bound to a variable that outlives the source String. This is
a best-effort check, not a guarantee — it's unsafe code.

## Interaction with Other Features

### Unique T

`Ptr T` is orthogonal to `Unique`. Per KERNEL §17.4: `Ptr` is
unmanaged memory. `Unique` is managed memory with ownership
guarantees. They don't interact.

However: a `Unique (Array T)` can be passed to C code via
`unsafe Array.as_ptr(arr)`. The Unique guarantee means no other
Kea code holds a reference, so C code can safely mutate the data.
This is the pattern for zero-copy FFI with mutable data.

### Effects and Handlers

FFI calls happen inside IO. Handlers can't intercept FFI calls
(they're not effects, they're raw function calls). This is correct:
FFI is the escape hatch from the effect system.

A safe wrapper re-enters the effect system:

```kea
fn read_file(path: String) -[IO, Fail IOError]> String
  let fd = unsafe c_open(path.as_c_str(), O_RDONLY)
  if fd < 0
    fail IOError.from_errno()
  -- ... read and return
```

The caller sees `-[IO, Fail IOError]>` — clean effects. The
unsafe C calls are invisible.

### @unboxed Types

`@unboxed` structs (KERNEL §12.6) can cross FFI directly because
they have C-compatible memory layout:

```kea
@unboxed
struct Vec2
  x: Float32
  y: Float32

@extern("c")
fn normalize_vec2(v: Vec2) -[IO]> Vec2  -- passed by value, C-compatible
```

This is important for numeric/SIMD interop.

## Definition of Done

- [ ] `@extern("c")` functions parse, type-check, and compile
- [ ] `@extern("c")` calls use C calling convention (verified with a C test library)
- [ ] `unsafe` blocks parse and enforce context tracking
- [ ] `@unsafe` functions require `unsafe` at call sites
- [ ] `Ptr T` operations work (read, write, offset, cast, null, alloc, free)
- [ ] `@link("name")` causes the library to be linked
- [ ] Static linking produces self-contained binaries
- [ ] `String.as_c_str`, `String.from_c_str`, `Bytes.as_ptr`, `Bytes.from_raw` work
- [ ] C type aliases (`CInt`, `CSize`, etc.) available in `ffi.kea`
- [ ] Cranelift bindings (`cranelift.kea`) can JIT-compile and execute a simple function
- [ ] AOT compilation with Cranelift bindings works
- [ ] ASAN/valgrind clean on all FFI tests
- [ ] At least one non-trivial C library binding (SQLite or similar) as validation
- [ ] Doc comments on all public FFI stdlib functions (Elixir/Rust quality)

## Risks

**Cranelift C API stability.** Cranelift may not have a stable C API.
If not, options: (a) write a thin C shim over Cranelift's Rust API,
compiled as a static library; (b) use Rust FFI directly (`@extern("rust")`);
(c) embed Cranelift source and compile it as part of `kea build`.
Option (a) is likely simplest — a ~500-line C shim that exposes the
subset we need.

**Platform differences.** C type sizes vary by platform (ILP32 vs
LP64 vs LLP64). The C type aliases must be target-dependent.
Cranelift already handles this — piggyback on its target triple.

**String lifetime safety.** `as_c_str` returning a dangling pointer
is the most common FFI bug in every language. The lint helps but
doesn't prevent it. Accept this as inherent to unsafe FFI — the
safe wrapper pattern is the mitigation.

**Callback FFI.** C libraries that take function pointer callbacks
(e.g., `qsort`) require wrapping Kea closures as C function pointers.
This requires a trampoline: a generated C-compatible function that
loads the closure environment and calls the Kea function. Defer to
post-1a unless a critical library needs it.
