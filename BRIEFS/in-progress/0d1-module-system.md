# Brief: Module System

**Status:** active
**Priority:** v1-critical
**Depends on:** 0d-codegen-pure (needs working codegen pipeline)
**Blocks:** stdlib-bootstrap (all tiers), 0e-runtime-effects, self-hosting
**Also read before implementing:**
- [KERNEL §11](../../docs/spec/KERNEL.md) — normative module specification
- [KERNEL §9.1](../../docs/spec/KERNEL.md) — method resolution and trait scoping
- [KERNEL Appendix C](../../docs/spec/KERNEL.md) — prelude traits
- [stdlib-bootstrap](stdlib-bootstrap.md) — the stdlib that this module system loads
- [packaging-ffi-comptime](../design/packaging-ffi-comptime.md) — future package system (not in scope here)
- [performance-backend-strategy](../design/performance-backend-strategy.md) — MIR must be backend-neutral; module resolution metadata must not be Cranelift-specific
- [runtime-introspection-mcp](../design/runtime-introspection-mcp.md) — the compilation API extraction in this brief is the foundation for "one engine, many consumers" (CLI, MCP, LSP, REPL)

## Motivation

The bootstrap compiler is single-file. You can't write a stdlib — or
any non-trivial program — without imports. This brief adds the minimal
module system needed to load stdlib `.kea` files and support multi-file
user programs.

This is NOT a package system. No `kea.toml`, no dependency resolution,
no version management, no `pub` enforcement. Those come later. This is:
parse `use`, find `.kea` files, compile them, link them together.

## Design (KERNEL §11)

### One file, one module (§11.1)

Each `.kea` file defines one module. The file path determines the
module name:

```
stdlib/list.kea       → List
stdlib/order.kea      → Order
src/http/server.kea   → Http.Server
src/app.kea           → App
```

### Imports (§11.2)

```kea
use List
use Http.Client.{get, post}
use Trees.Tree.{Leaf, Branch}
```

`use` brings names into scope. Selective imports with `{}` import
specific items. Without `{}`, the module name itself is in scope
for qualified access (`List.map`, `Http.Client.get`).

### Prelude (§11, Appendix C)

The following are in scope in every module without explicit `use`:

**Types:** `Int`, `Float`, `Bool`, `String`, `Unit`, `Never`,
`Option` (`Some`/`None`), `Result` (`Ok`/`Err`), `List`

**Traits (Appendix C):**
```
Show  Eq  Ord  From  Codec
Additive  Numeric
Concatenable  Monoid
Enumerable  Iterator  Foldable  Filterable
```

Prelude traits are available for unqualified method dispatch (§9.1).
Additional traits require explicit `use` to bring their methods into
scope.

### Trait import semantics (§9.1)

Trait methods only dispatch via dot syntax if the trait is in scope.
This is Gleam-style: importing a module doesn't automatically make
all of its trait impls available for method dispatch. You must
`use` the trait.

```kea
use Show          -- now x.show() works for any type with Show impl
use MyTrait       -- now x.my_method() works
```

Exception: prelude traits are always in scope. `x.show()` works
everywhere because `Show` is in the prelude.

**Qualified dispatch always works** regardless of imports:
`x.Show.show()` works even without `use Show`.

### No circular dependencies (§11.4)

Module imports form a DAG. Circular imports are a compile error
with a diagnostic showing the cycle.

### Struct-everything module model (§2.7)

Every `.kea` file implicitly defines a singleton struct whose name
comes from the filename. Top-level functions in the file are
inherent methods of that implicit struct. Type definitions in the
file are nested types in the module struct's namespace.

```
stdlib/list.kea       → implicit `struct List` with methods and types
stdlib/order.kea      → implicit `struct Order` with methods and types
src/app.kea           → implicit `struct App` with methods and types
```

**No explicit `struct List` needed at the top of `list.kea`.**
The file IS the struct. The KERNEL says "there are no bare functions,
every function belongs to a struct" (§2.7) and "modules are singleton
structs" — together these mean the file name gives the struct name.

**Same-name merge:** When a file defines a type whose name matches
the module name (e.g., `list.kea` defines `record List A`), the type
and the module struct are the same thing. `List` is both the type you
construct/pattern-match and the namespace for `List.map`. This is the
struct-everything model — the type is its own namespace.

```kea
-- stdlib/list.kea
-- Implicitly defines `struct List` from filename

record List A
  head: Option (A, List A)

fn map(_ self: List A, _ f: A -[e]> B) -[e]> List B
  -- ...

fn filter(_ self: List A, _ f: A -> Bool) -> List A
  -- ...
```

`List.map(xs, f)` works because `List` is the module struct and
`map` is a method. `xs.map(f)` works via UMS because `xs: List A`
matches the receiver type.

**Different-name types** are nested in the module namespace:

```kea
-- stdlib/order.kea
-- Implicitly defines `struct Order` from filename

enum Ordering = Lt | Eq | Gt

fn compare(_ a: A, _ b: A) -> Ordering where A: Ord
  -- ...
```

`Order.Ordering` is a nested type. `Order.compare` is a method.
Prelude re-export makes `Ordering` available unqualified.

**Namespace access uses dot.** PascalCase after a dot is a namespace
step; lowercase after a dot on a value is field/method. No `::` —
dot is dot (KERNEL §9.2). The parser distinguishes these lexically.

```kea
List.map(xs, f)        -- direct qualified call
xs.List.map(f)         -- UMS qualified
xs.map(f)              -- UMS unqualified
Order.Ordering.Lt      -- nested type access
xs.Show.show()         -- trait-qualified UMS
user.name              -- field access
```

**Nested modules as nested structs.** `http/server.kea` defines an
implicit `struct Server` inside the `Http` namespace. `Http.Server`
is the nested module struct. If `http/` is a directory without an
`http.kea` file, `Http` is a synthetic namespace struct (no methods).

## Implementation Plan

### Step 1: Parse `use` declarations

Extend the parser to handle `use` at the top of a file, before
any declarations. AST representation:

```rust
pub enum DeclKind {
    Use { path: Vec<String>, items: Option<Vec<String>> },
    // ... existing variants
}
```

`use List` → `Use { path: ["List"], items: None }`
`use Http.Client.{get, post}` → `Use { path: ["Http", "Client"], items: Some(["get", "post"]) }`

### Step 2: Module resolution

A `ModuleResolver` that maps module paths to `.kea` file paths.
Search order:

1. Stdlib directory (`stdlib/` relative to compiler binary, or
   `KEA_STDLIB_PATH` env var)
2. Project source directory (`src/` relative to the entry file,
   or current directory)

```rust
struct ModuleResolver {
    stdlib_path: PathBuf,
    source_roots: Vec<PathBuf>,
}

impl ModuleResolver {
    fn resolve(&self, module_path: &[String]) -> Result<PathBuf, ModuleNotFound>
}
```

Module path `Http.Server` resolves to `http/server.kea` (lowercase
path segments, `.` becomes `/`).

### Step 3: Dependency graph and topological sort

Given an entry file, walk `use` declarations recursively, building
a dependency DAG. Detect cycles (report as a compile error with the
cycle path). Topological sort determines compilation order.

```rust
struct ModuleGraph {
    modules: BTreeMap<ModulePath, ModuleNode>,
}

impl ModuleGraph {
    fn build(entry: &Path, resolver: &ModuleResolver) -> Result<Self, CycleError>
    fn compilation_order(&self) -> Vec<ModulePath>
}
```

### Step 4: Multi-module compilation with struct-everything

Compile modules in topological order. Each module's declarations
are registered into a shared `TypeEnv` (the infrastructure already
exists: `module_functions`, `module_type_schemes`, `module_aliases`
in the TypeEnv). After type-checking all modules, lower all to
HIR → MIR → Cranelift together.

The key change to the pipeline: instead of processing one `Module`,
process a `Vec<Module>` in dependency order, accumulating type
information across modules.

**Implicit module struct creation:** When compiling a module file,
the compiler must:

1. Derive the struct name from the filename (`list.kea` → `List`)
2. Register an implicit `Struct { name }` in the TypeEnv
3. Register all top-level functions as inherent methods of that struct
4. Register all type definitions as nested types in the struct's
   namespace
5. **Same-name merge:** If the file defines a type matching the
   module name (e.g., `list.kea` defines `record List A`), the type
   and the module struct are the same thing — don't create a separate
   wrapper struct. `List` is both the constructable type and the
   method namespace.
6. **Different-name types:** Nest under the module namespace.
   `order.kea` defining `enum Ordering` → `Order.Ordering`.

This is what makes `List.map(xs, f)` (direct qualified call) and
`xs.map(f)` (UMS unqualified) both work — `map` is an inherent
method of the `List` struct, and UMS resolution finds it via the
receiver type.

**Trait impl visibility:** All impls are globally visible for
bootstrap. When module A defines `impl Show for MyType`, that impl
is visible in module B regardless of imports. This matches Haskell's
instance model. Orphan rules and visibility restrictions are
deferred to post-bootstrap.

### Step 5: Prelude loading

The prelude is a set of stdlib modules auto-imported before user
code. Implementation: hardcode a list of prelude module paths.
Before processing user modules, load and compile the prelude
modules. Register their declarations into the TypeEnv. User code
sees prelude types and traits without `use`.

Prelude modules are compiled once per invocation and their
declarations are available to all user modules.

**Prelude re-exports are hardcoded.** The prelude brings specific
names into unqualified scope via a hardcoded list (e.g., `Ordering`
from `Order`, `Some`/`None` from `Option`). This is not a general
`pub use` mechanism — it's a bootstrap expedient. General re-export
syntax (`pub use`) is deferred to the packaging phase.

### Step 6: Intrinsic function support

Stdlib functions that bottom out in runtime operations need an
intrinsic mechanism. Design:

```kea
@intrinsic("__kea_string_length")
fn length(self: String) -> Int
```

Codegen recognizes `@intrinsic` and emits a direct call to a
Rust-provided runtime function instead of compiling a Kea body.
The runtime functions are linked into the JIT/AOT module.

Minimum intrinsic set for Tier 0 stdlib:
- String: `__kea_string_length`, `__kea_string_concat`,
  `__kea_string_slice`, `__kea_string_eq`
- Memory: `__kea_alloc`, `__kea_free`, `__kea_rc_retain`,
  `__kea_rc_release` (if not already provided by 0d)
- IO: `__kea_print` (minimal stdout for debugging)

## What transfers from Rill

`rill-eval` has a module loading system (`ModuleLoader` in
`rill/crates/rill-eval/src/module_loader.rs`) that resolves
import paths to files and manages dependency order. The logic
transfers; the implementation is different (compiled vs
interpreted).

## Testing

- **Parse tests:** `use` declarations parse correctly (bare,
  selective, nested paths)
- **Resolution tests:** module paths resolve to correct files
  given stdlib and source directories
- **Cycle detection:** circular imports produce clear error
  with cycle path
- **Multi-module type checking:** types defined in module A
  are usable in module B after `use A`
- **Trait scoping:** trait methods only dispatch when trait is
  in scope (via `use` or prelude)
- **Prelude tests:** prelude types and traits available without
  explicit `use`
- **Intrinsic tests:** `@intrinsic` functions compile and link
  correctly
- **Integration test:** compile a program that uses stdlib
  `List.map` and `Option.unwrap_or`
- **Resolution test matrix:** Write before implementing UMS +
  module dispatch. Cover every combination of:
  - Call form: direct qualified (`List.map(xs, f)`), UMS
    unqualified (`xs.map(f)`), UMS qualified (`xs.List.map(f)`)
  - Method kind: inherent method, trait method
  - Import state: not imported, `use Module`, `use Module.{name}`,
    prelude (implicit)
  - Module relationship: same module, cross-module
  This matrix is where subtle resolution bugs hide. Write the
  tests first, then implement.

## Definition of Done

- `use` declarations parse and resolve to `.kea` files
- Multi-file compilation works (dependency order, merged TypeEnv)
- Prelude loads automatically (Option, Result, List, core traits)
- `@intrinsic` functions compile to runtime calls
- At least one integration test: user `.kea` file imports stdlib
  modules and produces correct output
- Circular import detection with clear diagnostic
- `mise run check-full` passes

## Compilation API extraction

The `kea` CLI crate currently has no `lib.rs` — all pipeline
orchestration (parse, typecheck session setup, compilation) lives
in `main.rs`. The MCP server already duplicates the type-checking
setup independently.

**Hard requirement of 0d1: extract a public compilation API** from
`main.rs` into `crates/kea/src/lib.rs` (or a new `kea-compiler` crate).
The MCP server already duplicates session setup independently, and this
divergence is already causing bugs (phantom IO leak was partly surfaced
through MCP behaving differently from direct inference). With 0e adding
handler machinery that both CLI and MCP will need, two divergent setup
paths is a guaranteed source of subtle correctness issues. Extract once
before 0e, not after.

```rust
pub struct CompilationContext {
    pub modules: Vec<TypedModule>,
    pub type_env: TypeEnv,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn compile_module(source: &str, file_id: FileId) -> Result<CompilationContext, ...>
pub fn compile_project(entry: &Path) -> Result<CompilationContext, ...>
pub fn execute_jit(ctx: &CompilationContext) -> Result<i32, ...>
pub fn emit_object(ctx: &CompilationContext) -> Result<BackendArtifact, ...>
```

This matters because multi-module compilation adds real orchestration
complexity (dependency graph, prelude loading, merged TypeEnv). If
this logic stays in `main.rs`, every consumer (LSP, REPL, MCP, test
runner) must duplicate it. Extract once, import everywhere.

`main.rs` becomes a thin CLI wrapper. `kea-mcp` imports the same API
instead of duplicating session setup.

## Not in scope (deferred)

- Package manifest (`kea.toml`)
- Dependency resolution and version management
- `pub` enforcement — all items are accessible for bootstrap. However,
  the parser MUST accept `pub` and the module system MUST store
  visibility metadata on declarations. The stdlib uses `pub` from day
  one so it's correct when enforcement turns on (post-bootstrap). The
  metadata must be present in the compiled representation so that
  enforcement is a policy check, not a representation change.
- Separate compilation / incremental compilation
- Module caching / precompiled headers
- `@with` annotation on handler-shaped functions (deferred to 0h)

## Progress
- 2026-02-27 15:01: 0d1 kickoff started. Parser now accepts top-level `use` module declarations (legacy `import` retained as compatibility alias), with regression coverage for bare/nested/selective/alias `use` forms and mixed `use` + function declarations. This aligns source syntax with KERNEL §11 while preserving parser compatibility during the resolver migration.
- 2026-02-27 15:12: Module-resolution pipeline now runs in the CLI compile/run path: project entrypoints load dependency modules via `use`, detect circular imports, and typecheck modules in dependency order before merged lowering/codegen. Added integration tests for cross-file `use` execution and explicit cycle diagnostics.
- 2026-02-27 15:12: Stabilized merged-module lowering for cross-file codegen by keeping single-file behavior intact, preserving qualified module call metadata in `TypeEnv`, and handling cross-file span aggregation with synthetic module spans.
- 2026-02-27 15:16: Implemented explicit named-import scoping for project modules. `use Module.{name}` now binds bare symbols in the current module scope, while plain `use Module` only enables qualified access (`Module.name`). Added CLI integration regressions: named bare call succeeds and bare call without named import fails with `undefined variable`.
- 2026-02-27 15:30: Extracted compilation pipeline from `kea/src/main.rs` into reusable library API (`kea/src/lib.rs` + `kea/src/compiler.rs`). Public entrypoints now include `compile_module`, `compile_project`, `emit_object`, and `execute_jit`, with `main.rs` reduced to CLI parsing/linking + tests using shared library functions. This removes duplicate CLI-only orchestration and establishes a single import/typecheck/codegen setup path for downstream tooling consumers.
- 2026-02-27 15:34: `kea-mcp` now consumes shared declaration/session typecheck logic via `kea::process_module_in_env` instead of its prior in-crate duplicated module-processing path. This removed duplicated registration/typecheck/effect-contract logic and aligned MCP declaration semantics with CLI/library behavior while preserving existing MCP tool contracts and tests.
- 2026-02-27 15:36: Added prelude autoload scaffolding to project module collection: configured prelude modules are visited before entrypoint resolution (`KEA_PRELUDE_MODULES`, default `Prelude`), and missing prelude files are non-fatal for bootstrap transition. Added CLI integration regression proving `Prelude.*` qualified calls work without explicit `use` when a `stdlib/prelude.kea` module is present.
- 2026-02-27 16:12: Landed resolution-matrix implementation slice: parser now desugars qualified UMS chains (`x.Trait.method(...)`, `x.Core.Math.map(...)`) to qualified calls with receiver-first args; module alias resolution now requires explicit alias/import visibility (except explicit dotted module paths), and non-entry module alias/trait scope is restored after each module pass while retaining qualified function bindings needed for merged codegen. Added/updated parser regressions for qualified UMS desugaring and CLI matrix regressions for inherent/trait call forms across import states.
- 2026-02-27 16:41: Implemented trait-import scope plumbing for unqualified UMS dispatch. `use TraitModule` now marks owned traits in scope and imports trait method call targets; prelude module passes retain trait scope + trait method bindings so `x.traitMethod()` works without explicit `use` when provided by prelude. Updated resolution matrix expectations (trait unqualified cross-module now succeeds for `use Module` and prelude) and added CLI regression `compile_and_execute_prelude_trait_unqualified_method_without_use_exit_code`.
- 2026-02-27 16:43: Added module visibility metadata tracking to `TypeEnv` (`module_path + item -> public/private`) and wired compiler registration for functions, expr fns, traits, effects, records, aliases, opaques, and sum types. Added CLI regression `compile_project_tracks_module_item_visibility_metadata` to lock metadata persistence across multi-module project compilation.
- 2026-02-27 16:51: Wired hardcoded prelude re-export application in project compilation (`KEA_PRELUDE_REEXPORTS`, default `Order.Ordering,Option.Some,Option.None,Result.Ok,Result.Err`) so function-like entries can be rebound into unqualified scope with call/effect metadata preserved, and trait names listed there are marked in scope when owned by the referenced module. Added CLI regression `compile_project_accepts_unqualified_prelude_reexported_type_names` to lock unqualified prelude type usage (`Ordering`) across module boundaries.
- 2026-02-27 16:55: Implemented Step 4 struct-everything metadata plumbing in the shared compiler/type environment: each module now registers implicit module-struct info (`module path -> {name, merged_with_named_type}`) with same-name merge detection (e.g. `list.kea` + `type List = ...`), and top-level module functions are recorded as inherent methods of that module struct type. Added CLI regressions `compile_project_tracks_module_item_visibility_metadata` (extended with module-struct + inherent-method assertions) and `compile_project_marks_same_name_module_type_merge`.
- **Next:** Use the new module-struct/inherent-method metadata in UMS resolution policy so `use Module` can rely on explicit module struct ownership (instead of bare-name import side effects), then update the resolution matrix expectations/tests accordingly.
