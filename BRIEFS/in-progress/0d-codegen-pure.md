# Brief: Code Generation — Pure Subset

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0b-type-system-core, 0c-effect-handlers (at least Fail sugar)
**Blocks:** 0e-runtime-effects
**Also read before implementing:**
- [performance-backend-strategy](../design/performance-backend-strategy.md) — MIR must be backend-neutral, backend interface trait, ABI manifest, pass stats, layout stability rules, benchmark targets.
- [testing](testing.md) — Benchmark harness is a 0d Definition of Done item. Test runner design informs `kea test` infrastructure.

**Prerequisite (before Step 1):** Embed effect rows in `FunctionType`.
Currently `FunctionType` is `{ params, ret }` with effects tracked in
`TypeEnv` side-tables — inherited from Rill's purity/volatility model.
Kea's row-typed effects must be part of the structural type so that:
(a) `Display` shows `(Int) -[IO]> String` not `(Int) -> String`,
(b) MCP/LSP/REPL surface effects by displaying types (no side-channel),
(c) MIR can read effect signatures from types without side-table lookups,
(d) the formal agent's `Ty` inductive includes effect rows for theorems.
Change: add `effects: EffectRow` to `FunctionType`, update `Display`,
migrate `set_function_effect`/`set_function_effect_row` callers in
kea-infer to store effects in the type, update kea-mcp responses.
See [effects-platform-vision](../design/effects-platform-vision.md)
for why this matters for the "one semantic engine" principle.

**Note on 0c dependency:** This brief needs Fail sugar (`?`, `fail`,
`catch`) to work at the type level, but does NOT need the general
handler compilation machinery from 0e. `Fail` is special: because
its handler never resumes, it compiles to Result-passing (return
`Err`, branch on error). This is just control flow — no evidence
parameters, no continuations, no handler frames. Whoever implements
0d should compile Fail as Result-passing and not wait for 0e.

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

**Backend-neutrality constraint:** MIR must be defined independently
of Cranelift's builder API. MIR ops should represent Kea semantics
(retain, release, try_claim, freeze, effect_op, cow_branch) as
first-class operations — not as Cranelift function calls. The
Cranelift backend lowers MIR ops to Cranelift IR; a future backend
lowers the same MIR to its own representation. See
[performance-backend-strategy](../design/performance-backend-strategy.md)
for the full MIR contract requirements.

Minimum stable MIR op set (0d delivers these; 0e extends):
- Memory: `retain`, `release`, `move`, `borrow`, `try_claim`, `freeze`
- Mutation: `cow_update { unique_path, copy_path }`
- Effects: `effect_op { class: direct | dispatch | zero_resume }`
  (0d only needs `zero_resume` for Fail; 0e adds the rest)
- Handlers: `handler_enter`, `handler_exit`, `resume`
  (0d stubs these; 0e implements)
- Calls: `call { cc_manifest_id }` — references the ABI manifest

Key MIR design requirements for backend portability:
- Explicit value categories (unboxed value, heap-managed aggregate)
- Effect operations classified as MIR metadata, not encoded in
  the lowering
- Layout metadata as queryable side tables, not baked into IR nodes
- Calling convention expressed as an ABI manifest artifact (a
  concrete type/file consumed by codegen, not a comment)

### Step 3: Backend interface trait + Cranelift backend

Define a narrow backend interface trait:
- Input: validated MIR + layout tables + target config
- Output: object code / executable image + diagnostics + stats

Then implement the Cranelift backend as the first (and initially
only) implementation. Start from rill-codegen:
- Rename rill → kea
- Keep Cranelift builder/ISA/module setup
- Extend expression compilation for Kea's operations
- Add struct layout → Cranelift struct types
- Add enum layout → tagged unions
- Add function compilation (multi-expression bodies, not just
  scalar expressions)
- Add pattern matching → branch sequences

The backend interface is the stable contract. Cranelift is the
first implementation. Future backends (LLVM, Kea-native) implement
the same trait.

Step 3 deliverables:
- Backend interface trait defined and documented
- Cranelift backend implements the trait
- ABI manifest artifact: a concrete data type describing parameter
  classes (value/ref/evidence), return style, effect evidence
  placement. Codegen consumes this — it's not implicit knowledge
  baked into the Cranelift lowering
- Pass stats emitted: retain/release counts, allocation counts,
  handler classifications — machine-readable, per-function

### Step 4: AOT binary emission

Extend kea-codegen with AOT path:
- Use `cranelift-object` to produce object files
- Link with system linker (cc) to produce executables
- Entry point: compile `Main.main()` as the binary's main
- Runtime startup: initialize refcounting, set up IO handler

### Step 5: Refcounting + Update Fusion

**Refcounting** — MIR pass that inserts retain/release:
- Track value lifetimes through the MIR
- Insert `retain` when a value is copied (shared)
- Insert `release` when a value goes out of scope
- CoW for `~`: check refcount, branch to in-place or copy path
- Optimisation: elide retain/release pairs when possible (value
  is used exactly once)

**Update fusion** — MIR pass that merges chained `~` operations:

```kea
-- before fusion: 3 separate CoW checks + copies
user~{ name: "Alice" }~{ age: 30 }~{ email: "a@b.com" }

-- after fusion: 1 CoW check + 1 multi-field update
user~{ name: "Alice", age: 30, email: "a@b.com" }
```

Detection: identify sequences of `cow_update` MIR ops where the
output of one feeds directly into the next (SSA makes this
trivial — single-use intermediate values in a `~` chain).

Fusion: merge into a single `cow_update` with a combined field
set. One refcount check, one copy-or-mutate decision, all fields
updated together.

This is the primary fast path for the combinator pattern — fluent
method chains that return updated values. Without fusion, each
`.with_x()` call is a separate CoW check. With fusion, the
entire chain is one operation.

Constraints:
- No semantic change. Fused update must produce identical results.
- Only fuse when intermediate values have no other uses (SSA
  single-use check).
- Benchmark: chained `~` vs single `~` should show equivalent
  performance after fusion.

### Step 6: Basic stdlib

Runtime implementations for core types. In Phase 0, these are
Rust builtins compiled into the `kea` binary (like rill's
`BuiltinFn` pattern). In Phase 1+, they transition to Kea source
using the same module paths — the import interface stays stable.

**Layer 1 — core (pure, no effects):**
- `Int`, `Float`, `Bool`: unboxed, direct Cranelift types
- `String`: heap-allocated, refcounted, UTF-8
- `Option`, `Result`: tagged unions
- `Char`, `Bytes`, `()`: primitives
- Basic arithmetic, comparison, string operations

**Layer 2 — collections (pure, depends on core):**
- `List`: persistent (immutable), refcounted nodes
- `Map`, `Set`: placeholder stubs (real impls in 0h)

**Layer 3 — IO (requires `-[IO]>`):**
- `IO.stdout`: actual print (needed for hello world)
- `IO.read_file`, `IO.write_file`: basic file IO

The module namespace (`List.map`, `String.length`, `IO.stdout`)
is designed to be stable across the Rust-builtin → Kea-source
transition. User code that imports `List` works the same whether
`List` is a Rust builtin (Phase 0) or a Kea source module
(Phase 1+). See 0b brief item 3 on forward-looking module
resolution.

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
- Update fusion: chained `~` operations fuse into single update.
  Benchmark: chained `~` vs single `~` shows equivalent performance
- Backend interface trait exists with Cranelift as sole implementor
- ABI manifest is a concrete artifact consumed by codegen
- Pass stats (retain/release/alloc counts) emitted per function
- Benchmark baseline harness in-tree: at least pure numeric loop,
  string/collection transform, and allocation-heavy workload.
  Measured and recorded — no regression gates yet (baselines only),
  but the harness must exist so 0e can add gates
- `mise run check` passes

## Decisions

- **Full monomorphization for v0.** Every generic function is
  compiled once per concrete type instantiation. No type erasure,
  no dictionary passing, no hybrid strategy. This is what
  Cranelift expects and produces the best runtime code. The
  compilation speed cost is a scaling concern — at bootstrap size
  (~50K lines) it's fine. If monomorphization becomes a bottleneck
  later, known solutions exist (type erasure for cold paths,
  dictionary passing for polymorphic recursion), but don't build
  them until profiling shows you need them.

- **Refcount atomicity is effect-directed.** Functions whose
  effect set includes no concurrency effects (Send, Spawn, Par)
  emit non-atomic refcount operations. Functions with concurrency
  effects emit atomic operations. Values crossing thread
  boundaries (at Send.tell, Spawn.spawn, Par.map) are promoted
  to atomic at the boundary. See §12.2 discussion (pending).

## Optimization Contract

Type-driven codegen classes with benchmark gates. 0d establishes
the pure and Fail-only classes; 0e adds the handler classes.

| Class | Codegen strategy | Benchmark gate | Phase |
|-------|-----------------|----------------|-------|
| **Pure** (no effects) | Direct call, full inlining | Baseline. Must match hand-written C for tight loops | 0d |
| **Fail-only** | Result-passing (branch on error), never enters handler dispatch | Within 5% of pure for non-error path. **Codegen invariant: Fail must not use generic handler dispatch** | 0d |
| **Tail-resumptive** | Evidence parameter, resume = tail call. **Required fast path: inline to direct call when handler is statically known** | Within 2x of parameter-passing baseline | 0e |
| **Non-tail** | CPS or segmented stack (full continuations) | Within 10x of direct call (this is the expensive case) | 0e |

Precision notes:
1. Closed-row field access compiles to known offset **after monomorphisation**.
   Open rows use polymorphic representation until specialised.
2. Fail-only near-zero overhead is only true when lowered to Result
   branch form. This is a codegen invariant — Fail must never enter
   generic handler dispatch.

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

## Progress
- 2026-02-26: Step 0 prerequisite slice landed in code: `FunctionType` now includes `effects: EffectRow` as structural type data; `Type` display/substitution/free-var traversal include function effects; infer/module env updates function type effects via `set_function_effect_row`; MCP now surfaces effectful function signatures via normal type display.
- 2026-02-26: Regression covered: phantom `IO` leakage in MCP declaration mode fixed by row-native declaration validation + MCP row-native effect plumbing.
- **Next:** Start Step 1 with `kea-hir` crate scaffolding and initial typed/desugared lowering for a minimal function/expression subset.
