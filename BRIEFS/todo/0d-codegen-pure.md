# Brief: Code Generation — Pure Subset

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0b-type-system-core, 0c-effect-handlers (at least Fail sugar)
**Blocks:** 0e-runtime-effects

## Motivation

Compile and run pure Kea programs natively. This is the first time
Kea source becomes executable code. The Cranelift pipeline from
rill-codegen (2,276 LOC) transfers directly — it's a JIT compiler
for scalar expressions. We need to extend it to handle Kea's full
pure subset and add AOT binary emission.

## What transfers from Rill

**rill-codegen** (2,276 LOC):
- `compiler.rs` (2,035 LOC): JIT compiler using Cranelift. Compiles
  expressions to native code for integer and floating-point
  operations. The Cranelift builder setup, ISA configuration,
  module creation, and function compilation patterns transfer
  directly. Expression compilation for arithmetic, comparisons,
  and function calls transfers.
- `types.rs` (226 LOC): Type mappings from semantic types to
  Cranelift IR types. Extend for Kea's type system.

**rill-mir** (161 LOC — small but structural):
- MIR design informs Kea's intermediate representation. The
  optimisation pass structure (even if passes are different)
  provides the framework.
- DataFusion-specific lowering doesn't transfer.

**rill-eval** (structural reference):
- The evaluator's stdlib implementations (collections, string ops,
  IO patterns) inform what the compiled stdlib needs to do.
- The evidence system for trait dispatch informs how to compile
  trait method calls.

## What's new (not in Rill)

1. **AOT binary emission.** Rill only has JIT. Kea needs
   `kea build file.kea → native binary`. Cranelift supports
   this via `cranelift-object` (produces object files) + system
   linker. The Cranelift setup is different from JIT but the
   IR generation is the same.

2. **Struct layout and enum layout.** Rill compiles scalar
   expressions. Kea needs full struct allocation, field access,
   and tagged union representation for enums.

3. **Pattern matching compilation.** Decision trees from match
   expressions → branch sequences in Cranelift IR.

4. **Refcounting insertion.** Retain/release calls at the right
   points. This is a MIR pass — annotate where values are
   created, copied, and dropped, then insert RC operations.

5. **Copy-on-write for functional update (~).** Runtime refcount
   check → in-place or copy path.

6. **Basic stdlib runtime.** Int, Float, String, Bool, List,
   Option, Result — enough to write real programs.

## Implementation Plan

### Step 1: kea-hir crate

Create `crates/kea-hir/`. The HIR is the typed, desugared AST:
- All names resolved
- All types annotated (from inference)
- Sugar expanded (method calls → qualified calls, `?` → match)
- Effect annotations attached

This is a new crate (no rill equivalent). It sits between the
type checker output and the MIR.

### Step 2: kea-mir crate

Create `crates/kea-mir/`. Use rill-mir as structural reference:
- Flat, SSA-like IR suitable for optimisation and codegen
- Explicit control flow (no nested expressions)
- Explicit memory operations (alloc, deref, copy)
- Refcounting annotations

### Step 3: kea-codegen crate — JIT path

Copy rill-codegen. Then:
- Rename rill → kea
- Keep Cranelift builder/ISA/module setup
- Extend expression compilation for Kea's operations
- Add struct layout → Cranelift struct types
- Add enum layout → tagged unions
- Add function compilation (multi-expression bodies, not just
  scalar expressions)
- Add pattern matching → branch sequences

### Step 4: AOT binary emission

Extend kea-codegen with AOT path:
- Use `cranelift-object` to produce object files
- Link with system linker (cc) to produce executables
- Entry point: compile `Main.main()` as the binary's main
- Runtime startup: initialize refcounting, set up IO handler

### Step 5: Refcounting

MIR pass that inserts retain/release:
- Track value lifetimes through the MIR
- Insert `retain` when a value is copied (shared)
- Insert `release` when a value goes out of scope
- CoW for `~`: check refcount, branch to in-place or copy path
- Optimisation: elide retain/release pairs when possible (value
  is used exactly once)

### Step 6: Basic stdlib

Runtime implementations for core types:
- `Int`, `Float`, `Bool`: unboxed, direct Cranelift types
- `String`: heap-allocated, refcounted, UTF-8
- `List`: persistent (immutable), refcounted nodes
- `Option`, `Result`: tagged unions
- `IO.stdout`: actual print (needed for hello world)
- Basic arithmetic, comparison, string operations

### Step 7: CLI

Create `crates/kea/` (the binary crate):
- `kea build file.kea` → compile to native binary
- `kea run file.kea` → compile and execute (JIT path)
- Parse → typecheck → lower to HIR → lower to MIR →
  codegen → emit/execute

## Testing

- Compile and run: arithmetic, let bindings, function calls
- Structs: construction, field access, functional update
- Enums: construction, pattern matching, exhaustiveness
- Functions: recursion, closures, higher-order functions
- Row polymorphism: functions accepting open rows work at runtime
- Refcounting: values are freed when no longer referenced
- CoW: functional update is in-place when refcount is 1
- AOT: `kea build` produces a working binary
- JIT: `kea run` executes correctly
- Snapshot tests: compiled output matches evaluator output for
  the same programs

## Definition of Done

- `kea run hello.kea` prints "hello world"
- Pure Kea programs with structs, enums, pattern matching,
  closures, and row polymorphism compile and run correctly
- Both JIT and AOT paths work
- Refcounting keeps memory bounded (no leaks on simple programs)
- `mise run check` passes

## Open Questions

- Do we need an evaluator (kea-eval) for bootstrap, or can we
  go straight to codegen? (The roadmap has kea-eval as a crate
  but the ROADMAP §0d goes straight to codegen. Proposal: skip
  the tree-walking evaluator for now. Use rill-eval patterns as
  reference for stdlib behavior, but compile from the start.)
- Closure representation: boxed closures (simple, heap-allocated)
  or unboxed (specialised per capture set)? (Proposal: boxed
  closures first. Optimise later.)
- String representation: small-string optimisation from the start,
  or simple heap allocation? (Proposal: simple heap allocation.
  SSO is an optimisation for later.)
