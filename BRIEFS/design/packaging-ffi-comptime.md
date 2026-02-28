# Brief: Packaging, FFI, and Comptime

**Status:** design
**Priority:** Phase 1-2 (FFI in Phase 1, packaging in Phase 2, comptime in Phase 1+)
**Depends on:** 0d-codegen-pure (Cranelift backend), 0g-advanced-types (associated types for traits, @derive infrastructure)
**Blocks:** ecosystem growth, third-party packages, Arrow integration

## Motivation

Three interconnected concerns that determine whether Kea has an
ecosystem or remains a solo project:

1. **FFI:** How does Kea call C/Rust code? How do native libraries
   integrate? Arrow integration depends on this.
2. **Packaging:** How are Kea packages published, discovered,
   installed? What security guarantees does the registry provide?
3. **Comptime:** How does Kea do code generation without proc
   macros, build scripts, or install scripts?

The effect system gives Kea unique answers to all three.

## Part 1: FFI

### C FFI (Day One)

Kea compiles via Cranelift, which means we control the calling
convention. C ABI interop is the foundation:

```kea
-- Declare a foreign function with C calling convention
extern "C" fn sqlite3_open(_ filename: Ptr U8, _ db: Ptr (Ptr Sqlite3)) -> Int

-- Wrapper with Kea types and effects
struct Sqlite
  fn open(_ path: String) -[IO, Fail SqliteError]> Sqlite
    let db = unsafe Ptr.null()
    let rc = sqlite3_open(path.as_c_str(), Ptr.addr_of(db))
    if rc != 0
      fail SqliteError.from_code(rc)
    Sqlite { handle: db }
```

Key decisions:

- **`extern "C"` for foreign declarations.** Same syntax as Rust.
  Maps directly to Cranelift's C calling convention support.
- **`unsafe` blocks for raw pointer operations.** FFI is
  inherently unsafe. The `unsafe` keyword marks the boundary.
  Inside a Kea wrapper, the unsafe operations are contained and
  the public API is safe.
- **No dlopen/runtime loading.** Unlike Rill's extension model,
  Kea uses static linking for native code. This is simpler, more
  portable, and eliminates a class of runtime errors.
- **IO effect on FFI wrappers.** Foreign functions that do IO
  must declare it. The effect system tracks FFI side effects.

### Arrow Integration (Library, Not Runtime)

Kea's row polymorphism maps naturally to Arrow schemas. But Arrow
is a library package (`kea-arrow`), not baked into the compiler.

```kea
-- Arrow schema IS a Kea row type
type UserSchema = { name: String, age: Int, email: Option String }

-- Zero-copy columnar operations via Arrow C Data Interface
struct Arrow
  fn read_parquet(_ path: String) -[IO, Fail ArrowError]> Table T
    where T: Schema

  fn filter(_ table: Table T, _ pred: (Row T) -> Bool) -> Table T

  fn select(_ table: Table T) -> Table { fields | r }
    where { fields | r } <: T
```

Row polymorphism gives type-safe column selection — `select`
returns a table with only the requested columns, fully typed.
No equivalent in any other language's Arrow bindings.

The Arrow C Data Interface enables zero-copy exchange between
Kea and any Arrow-compatible library (DuckDB, DataFusion, Polars)
without serialization overhead.

### What Transfers from Rill

Rill's `rill-extension-api` C ABI is the wrong model for Kea
(dlopen, runtime loading, JSON metadata). But several pieces
inform the design:

- **Arrow C Data Interface types** (`FFIArrowSchema`,
  `FFIArrowArray`) — the zero-copy exchange protocol transfers
- **Value marshalling patterns** — converting between language
  values and C ABI types
- **Opaque handle pattern** — wrapping C pointers in safe Kea
  types with custom drop

Rill's extension loader, dlopen machinery, and JSON metadata
system do NOT transfer.

## Part 2: Packaging

### Package Manifest (`kea.toml`)

```toml
[package]
name = "my-app"
version = "0.1.0"
kea = "0.1"
entry = "src/main.kea"

[dependencies]
http = "1.2.0"
json = { version = "0.5", features = ["streaming"] }
arrow = { git = "https://github.com/kea-lang/kea-arrow" }
```

### Security: Effects as Permissions

This is Kea's unique contribution to package security. Every
package's public API declares its effects. The registry displays
effect badges:

- **Pure** (`->`): provably no IO, no network, no filesystem.
  Cannot phone home. Cannot exfiltrate data. The compiler proves
  this — not a sandbox, not a trust model, a proof.
- **IO** (`-[IO]>`): touches the outside world. Visible to users
  before they install.
- **Send/Spawn** (`-[Send, Spawn]>`): uses concurrency.
- **Fail** (`-[Fail E]>`): can fail with specific error types.

A pure math library that suddenly starts doing IO in a patch
release? The compiler catches it. The registry flags it. Users
see it before they upgrade.

### No Install Scripts. No Build Scripts. No Exceptions.

The npm ecosystem has 500,000+ malicious packages (2024). The
root vulnerability: install scripts that run arbitrary code.
Rust's build.rs is the same class of problem (arbitrary code at
compile time, unsandboxed).

Kea eliminates this entire attack surface:

- **No install scripts.** Packages are source code. Installing
  a package means downloading source and compiling it with the
  Kea compiler. No code runs during installation.
- **No build scripts.** If a package needs native code, it ships
  precompiled binaries for supported platforms or uses C FFI
  with static linking. The build process is the Kea compiler,
  nothing else.
- **Comptime replaces proc macros.** Code generation happens
  inside the compiler via the `Compile` effect (see Part 3).
  No arbitrary code execution. No separate compilation phase.

### Registry Architecture

Drawing from Go's module proxy (the best current model):

- **Immutable versions.** Once published, a version cannot
  change. Content-addressed by cryptographic hash.
- **Transparency log.** Every publish event recorded in a
  tamper-evident, append-only log. Same principle as Go's
  `sum.golang.org`.
- **Trusted publishing.** OIDC-based authentication from CI
  (GitHub Actions, etc.). No long-lived API tokens. crates.io
  adopted this July 2025.
- **Lockfile** (`kea.lock`): exact versions + hashes, checked
  into the repo. Build fails if checksums don't match.
- **No mutable packages.** Unlike npm, you cannot push a new
  version over an existing one. Yank (soft-delete) is supported
  for security advisories.

### Dependency Resolution

Semver-based. Minimal version selection (Go's model) rather than
maximal (npm/cargo's model). This means builds are reproducible
without a lockfile — the lockfile adds an extra layer of assurance
but isn't strictly required.

## Stdlib: Not a Package, But Uses Package Structure

Stdlib is not distributed via the package registry. It ships
with the `kea` binary. But it uses the same module conventions
as user packages — the import path for `List.map` works whether
the implementation is a Rust builtin (Phase 0) or Kea source
(Phase 1+).

### Stdlib Layers

```
kea-core        -- Int, Float, Bool, String, Option, Result, Char, Bytes
                -- pure (->), compiler intrinsics for primitive ops

kea-collections -- List, Map, Set, Iterator, Foldable, Enumerable
                -- pure (->), depends on kea-core

kea-io          -- File, Net, Process, Env, Clock
                -- requires -[IO]>, depends on kea-core

kea-serial      -- Json, Toml, MsgPack, Csv, Encode/Decode
                -- requires -[Fail DecodeError]>, depends on kea-core

kea-test        -- test runner, assertions, effect-aware mocking
                -- depends on kea-core, kea-io
```

### Phase Transition

| Phase | Stdlib is... | Module resolution |
|-------|-------------|-------------------|
| 0 (bootstrap) | Rust `BuiltinFn` in compiler binary | Compiler knows builtin names |
| 1 (self-hosting) | Kea source, compiled into `kea` binary | Same import paths, backed by `.kea` files |
| 2+ (ecosystem) | Kea source, same structure as user packages | Same module system as third-party code |

The module namespace is the stable interface. User code that
writes `import List` or calls `List.map(xs, f)` works identically
across all phases. The 0b brief (item 3) and 0d brief (Step 6)
both capture this forward-looking constraint.

## Part 3: Comptime — Compiler Layer Interface as Code Generation

### The Insight

The compiler pipeline is a set of typed APIs: parse → AST →
type-check → typed AST → HIR → MIR → codegen. Comptime is
"call compiler APIs at compile time."

`@derive` is not magic — it's a compile-time function. It takes
a type descriptor and emits implementation code. Today it's a
hardcoded compiler pass. Tomorrow it's a Kea function with the
`Compile` effect.

### The Compile Effect

```kea
effect Compile
  -- Type introspection
  fn type_info(_ name: String) -> TypeInfo
  fn fields(_ ty: TypeInfo) -> List FieldInfo
  fn variants(_ ty: TypeInfo) -> List VariantInfo
  fn effects(_ fn_name: String) -> EffectRow
  fn traits(_ ty: TypeInfo) -> List TraitInfo
  fn impls(_ trait_name: String, _ ty: TypeInfo) -> Option ImplInfo

  -- Code emission
  fn emit_fn(_ decl: FnDecl) -> Unit
  fn emit_impl(_ impl_decl: ImplDecl) -> Unit
  fn emit_type(_ ty_decl: TypeDecl) -> Unit

  -- Diagnostics (comptime can report errors/warnings)
  fn error(_ msg: String, _ loc: SourceLoc) -> Unit
  fn warning(_ msg: String, _ loc: SourceLoc) -> Unit
```

### @derive as a Compile Function

```kea
-- @derive(Encode) desugars to a comptime call:
struct Encode
  fn derive(_ ty: TypeInfo) -[Compile]> Unit
    let fields = Compile.fields(ty)
    let encode_body = fields.map(|f|
      FnCall("write_key", [StringLit(f.name)]),
      FnCall("encode", [FieldAccess("self", f.name)])
    )
    Compile.emit_impl(ImplDecl {
      trait_name: "Encode",
      for_type: ty.name,
      methods: [{
        name: "encode",
        params: [("self", ty.name), ("w", "FormatWriter")],
        body: encode_body
      }]
    })
```

### Why This is Better Than Every Alternative

| Approach | Type info? | Safe? | Typed output? |
|----------|-----------|-------|---------------|
| Rust proc macros | No (token streams) | No (arbitrary code) | No |
| Zig comptime | Yes (reified types) | Yes (no IO) | Yes |
| Template Haskell | Yes (AST) | No (IO allowed) | Partial |
| Lisp macros | No (S-expressions) | No | No |
| **Kea comptime** | **Yes (TypeInfo)** | **Yes (effect-enforced)** | **Yes** |

Kea's comptime is:
- **Type-aware.** Comptime functions receive `TypeInfo`, not
  token streams. They know field names, types, effect signatures.
- **Effect-safe.** The `Compile` effect does NOT include `IO`.
  A comptime function provably can't read your filesystem, phone
  home, or mine crypto. Not a sandbox — a proof.
- **Typed output.** Comptime emits typed declarations (`FnDecl`,
  `ImplDecl`), not raw text. The compiler type-checks the output.
  Malformed code is caught at compile time, not at runtime.

### Comptime Replaces

- **Rust proc macros.** Kea's comptime functions are typed,
  safe, and fast. No separate compilation. No build.rs.
- **Go's `go generate`.** Kea's comptime runs inside the
  compiler. No manual step. No out-of-band code generation.
- **npm install scripts.** There are none. Comptime is the
  only code generation mechanism, and it's sandboxed by effects.
- **Rill's extension metadata.** Rill used JSON metadata to
  declare extension types. Kea's comptime can introspect types
  directly — no metadata format needed.

### Self-Hosting Completes the Circle

Once Kea self-hosts, the compiler IS Kea code. Comptime doesn't
need a special evaluator — it calls the same functions the
compiler uses. The compiler layer interface and the comptime API
are literally the same code.

Before self-hosting (Phase 0), `@derive` is a hardcoded compiler
pass in Rust for the core traits (`Encode`, `Decode`, `Show`,
`Eq`, `Ord`, `Hash`). But the interface — `TypeInfo`, `FieldInfo`,
`VariantInfo` — should be designed now so that when comptime lands,
`@derive` becomes a regular function.

### The TypeInfo API (Design Now, Implement Later)

These types should exist in `kea-types` from Phase 0, even if
comptime doesn't land until Phase 1+:

```kea
struct TypeInfo
  name: String
  kind: TypeKind           -- Struct, Enum, Alias
  type_params: List String
  fields: List FieldInfo   -- for structs
  variants: List VariantInfo -- for enums

struct FieldInfo
  name: String
  type_name: String
  type_info: TypeInfo
  position: Int
  has_default: Bool

struct VariantInfo
  name: String
  payloads: List FieldInfo
  position: Int
```

These are the reified type representations that comptime functions
operate on. They're also what `@derive` uses internally — just
formalized as a data type rather than ad-hoc compiler code.

## Decisions

- **No dlopen extensions.** Unlike Rill, Kea does not load
  shared libraries at runtime. Native interop is via C FFI
  with static linking.

- **Arrow as a library package.** Not baked into the compiler
  or runtime. Row polymorphism gives type-safe Arrow schemas
  as a natural consequence of the type system.

- **No install scripts. No build scripts. No proc macros.**
  The entire supply chain attack surface is eliminated.
  Comptime via `Compile` effect is the only code generation
  mechanism.

- **Effects as package permissions.** Packages declare their
  effects. The registry displays them. Pure packages are
  provably safe. This is unique to Kea.

- **Immutable packages + transparency log + trusted publishing.**
  The gold standard from Go and crates.io, adopted from day one.

- **Minimal version selection.** Go's model. Reproducible
  builds without a lockfile.

- **TypeInfo API designed in Phase 0.** Even though comptime
  lands later, the type representations are designed now so
  @derive can transition from hardcoded pass to comptime
  function without breaking changes.

## Implementation Timeline

### Phase 0 (now)
- Design `TypeInfo`, `FieldInfo`, `VariantInfo` types
- Hardcoded `@derive` for `Show`, `Eq`, `Ord`, `Hash`
  using these types internally

### Phase 1 (self-hosting)
- C FFI (`extern "C"` declarations, `unsafe` blocks)
- Cranelift C calling convention support
- `TypeInfo` reified at compile time
- Comptime evaluator (interpret `Compile` effect)
- `@derive` transitions from hardcoded to comptime function

### Phase 2 (ecosystem)
- Package registry (immutable, transparency log, OIDC)
- `kea pkg` CLI commands
- `kea.toml` + `kea.lock`
- `kea-arrow` first-party package
- Effect badges in registry

## Open Questions

- **Should `Compile` effect include `Fail`?** A comptime function
  that encounters an error (e.g., deriving Encode for a type with
  a non-serializable field) needs to report it. Options: (a)
  `Compile` includes diagnostic emission as operations (proposed
  above), (b) comptime functions can `fail` with compile errors.
  Proposal: both — `Compile.error` for warnings/notes,
  `Fail CompileError` for fatal errors that abort the derive.

- **Comptime execution model.** Interpreted (tree-walk the
  comptime function at compile time) or compiled (compile the
  comptime function with Cranelift, then run it)? Zig interprets.
  Rust proc macros compile to native code. Interpretation is
  simpler and safer. Compilation is faster for complex derives.
  Proposal: start with interpretation (simpler, sufficient for
  @derive), optimise later if needed.

- **Should packages be able to define new `@derive` macros?**
  If yes, a package like `kea-json` could provide
  `@derive(JsonEncode)`. This requires comptime functions to be
  invokable from other packages — which means the `Compile`
  effect must be available in library code, not just the compiler.
  Proposal: yes. This is the whole point. A comptime function is
  just a function with the `Compile` effect. The package system
  ensures it can't do IO.

- **C FFI safety model.** Should `extern "C"` functions require
  `unsafe` at the call site (Rust's model), or should the wrapper
  function's effect signature be sufficient (if it declares IO,
  the caller knows it has side effects)? Proposal: require
  `unsafe` for raw FFI calls. The safe wrapper pattern — unsafe
  inside, safe+effectful outside — is the intended usage.

- **Static vs dynamic linking for native deps.** Static linking
  is simpler and more portable. Dynamic linking allows sharing
  libraries across packages. Proposal: static by default, dynamic
  opt-in for system libraries (libc, OpenSSL).
