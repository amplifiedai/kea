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
`x.Show::show()` works even without `use Show`.

### No circular dependencies (§11.4)

Module imports form a DAG. Circular imports are a compile error
with a diagnostic showing the cycle.

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

**As part of 0d1, extract a public compilation API** from `main.rs`
into `crates/kea/src/lib.rs` (or a new `kea-compiler` crate):

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
- `pub` enforcement (all items public for bootstrap)
- Separate compilation / incremental compilation
- Module caching / precompiled headers
