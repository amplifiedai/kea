# Brief: Module System

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0d-codegen-pure (needs working codegen pipeline)
**Blocks:** stdlib-bootstrap (all tiers), 0e-runtime-effects, self-hosting
**Also read before implementing:**
- [KERNEL §11](../../docs/spec/KERNEL.md) — normative module specification
- [KERNEL §9.1](../../docs/spec/KERNEL.md) — method resolution and trait scoping
- [KERNEL Appendix C](../../docs/spec/KERNEL.md) — prelude traits
- [stdlib-bootstrap](stdlib-bootstrap.md) — the stdlib that this module system loads
- [packaging-ffi-comptime](../design/packaging-ffi-comptime.md) — future package system (not in scope here)

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

### Step 4: Multi-module compilation

Compile modules in topological order. Each module's declarations
are registered into a shared `TypeEnv` (the infrastructure already
exists: `module_functions`, `module_type_schemes`, `module_aliases`
in the TypeEnv). After type-checking all modules, lower all to
HIR → MIR → Cranelift together.

The key change to the pipeline: instead of processing one `Module`,
process a `Vec<Module>` in dependency order, accumulating type
information across modules.

### Step 5: Prelude loading

The prelude is a set of stdlib modules auto-imported before user
code. Implementation: hardcode a list of prelude module paths.
Before processing user modules, load and compile the prelude
modules. Register their declarations into the TypeEnv. User code
sees prelude types and traits without `use`.

Prelude modules are compiled once per invocation and their
declarations are available to all user modules.

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
- **Next:** Wire module resolution + dependency DAG into the `kea` compilation pipeline (replace current "parsed but not wired" import warning), then add multi-file integration tests with cycle diagnostics.
