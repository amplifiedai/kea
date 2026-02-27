# Brief: Code Generation — Pure Subset

**Status:** active
**Priority:** v1-critical
**Depends on:** 0b-type-system-core, 0c-effect-handlers (at least Fail sugar)
**Blocks:** 0d1-module-system, 0e-runtime-effects
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

6. **Primitive operations as Cranelift-native ops.** Int arithmetic,
   Float arithmetic, Bool logic, comparisons — these are direct
   Cranelift instructions. The Kea-visible API surfaces for these
   primitives come from stdlib `.kea` files (see stdlib-bootstrap
   brief), but the operations themselves are Cranelift-native.
   String operations require `@intrinsic` runtime functions.

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
- Tail calls: self-recursive function doesn't overflow on large input
- Lambda syntax: `|x| -> x * 2` parses, `(x) -> x * 2` is rejected
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
- Tail call optimization: self-recursive tail calls use `return_call`,
  no stack overflow on `factorial(100000)`
- Lambda syntax matches KERNEL §10.3: `|x| -> expr`, not `(x) -> expr`
- Parametric ADTs parse: `type Option a = Some(a) | None`
- Row type annotations parse: `fn f(x: { name: String | r }) -> String`
- Trait type parameters parse: `trait Show a`
- Higher-order function calls don't leak phantom IO
- Curried higher-order application propagates effects (see §5.1 below)
- Effect row union is idempotent: no duplicate labels (see §5.2 below)
- Parametric type annotations in params: `fn f(opt: Maybe Int) -> Int`
- `Never` bottom type for diverging operations (`Fail.fail`)
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

- **Bootstrap IR tier.** The Rust HIR/MIR types built in 0d are
  InternalIR (KERNEL §15.1) — no stability promise, compiler-private.
  When Kea self-hosts, these same IRs become Kea types with stability
  tiers: StableHIR (versioned, row-extensible, for recipes) and
  UnstableMIR (for backends). Design the Rust types with this future
  in mind — clean node enums, no Cranelift types leaking into MIR
  node definitions — but don't build the versioning/row-extensibility
  machinery now. See [ir-recipes-grammar-convergence](../design/ir-recipes-grammar-convergence.md).

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

## Tail Call Optimization

Self-recursive tail calls must be optimized. Kea is a functional
language — recursive style is idiomatic. Without TCO, `factorial(100000)`
blows the stack.

Cranelift supports `return_call` (tail call instruction), stabilized
in 2024. Implementation:

1. **Detect tail position in MIR.** A call is in tail position when
   its result is the function's return value with no intervening work.
   For self-recursion this is straightforward — match `return call(self, args)`.
2. **Emit `return_call` in Cranelift.** Replace `call` + `return` with
   `return_call`. Cranelift handles the stack frame reuse.
3. **Scope: self-recursion first.** This covers `factorial`, `fold`,
   `traverse`, and most recursive patterns. Mutual tail calls (A calls
   B in tail position, B calls A in tail position) can be added later
   if needed — same mechanism, broader detection.

Refcounting interaction: release calls on out-of-scope values must be
inserted BEFORE the tail call, not after. The MIR pass that inserts
retain/release needs to be aware of tail position.

**This is a v0 deliverable.** A functional language without TCO is
broken for idiomatic use.

## Parser Gaps (spec vs implementation)

These are syntax features the inference engine already supports but
the parser doesn't accept. They block writing real Kea programs.

### 1. Lambda syntax (KERNEL §10.3)

**Current parser:** `(x) -> expr` and `(x, y) -> expr`
**Spec:** `|x| -> expr` and `|a, b| -> a + b`

The parser must be updated to match the spec. The `|...|` delimiter
syntax is better:
- Unambiguous — parens are overloaded with grouping, tuples, calls
- Visually distinct — lambdas are instantly recognizable
- Consistent with Rust/Ruby convention for closures

The `(x) -> expr` form should become a parse error (or at minimum a
deprecation warning) once `|x| -> expr` is implemented.

### 2. Parametric ADTs — CRITICAL

`type Option a = Some(a) | None` fails to parse. Only monomorphic
enums work (`type Color = Red | Green | Blue`). The type parameter
after the type name isn't recognized.

This is the #1 gap. Without parametric ADTs you can't write `Option`,
`Result`, `List`, or any generic data structure. The inference engine
already supports type parameters — this is purely a parser fix.

Test: `type Option a = Some(a) | None` followed by
`fn map(m: Option, f: Fun(Int, Int)) -> Option` should parse and
type-check.

### 3. Row type syntax in annotations — CRITICAL

`fn greet(person: { name: String | r }) -> String` fails to parse.
Row types in type annotations aren't recognized — the `{` is not
accepted as a type start.

Row polymorphism is Kea's core differentiator and you can't spell
row types in function signatures. The inference engine has full row
support (Rémy unification) — this is purely a parser gap.

Test: `fn greet(p: { name: String | r }) -> String` should parse.

### 4. Trait type parameters

`trait Show a` fails. Only `trait Show` (no params) parses. Can't
define parametric traits.

Test: `trait Show a` with `fn show(x: a) -> String` should parse.

### 5. Phantom IO leak on higher-order calls — SOUNDNESS

Calling a function value (`f(x)` where `f: Fun(a, b)`) injects
phantom `IO` into the effect row. Every higher-order function
appears effectful. **This is a soundness issue, not just a display
bug** — it masks real effects with phantom IO.

**Root cause diagnosed.** The effect tracking side-table doesn't
read effect rows from the structural function type. Precise location:

- `typeck.rs:7490` — `bind_let_pattern_effect_metadata`: when a
  let-binding's RHS returns a function type (e.g. `let f = make_emitter()`
  where `make_emitter() -> fn(Int) -[Emit]> Unit`), the effect row
  from the returned function type is NOT stored as `f`'s callable
  effect metadata.

- `typeck.rs:7462-7467` — `infer_callable_value_effect_row`: when
  `f(42)` is called, `f` has no stored effect metadata, so the
  function falls back to `unknown_effect_row(next_effect_var)`.
  This fresh variable gets collapsed to IO by the legacy lattice.

- Same issue at `typeck.rs:7483` for field-access callable paths.

**The evil test case (escaping effectful closure):**

```kea
effect Emit
  fn emit(val: Int) -> Unit

fn make_emitter() -> fn(Int) -[Emit]> Unit
  (x: Int) -> Emit.emit(x)

fn trap() -> Unit        -- should ERROR: unhandled Emit
  let f = make_emitter() -- f's type is fn(Int) -[Emit]> Unit
  f(42)                  -- should require [Emit], gets [IO] instead
```

`make_emitter` correctly infers `() -> (Int) -[Emit]> ()`. But
`trap` infers `() -[IO]> ()` instead of `() -[Emit]> ()`. The
`Emit` effect is present in the structural type but invisible to
the effect tracker.

**Fix:** In `bind_let_pattern_effect_metadata`, when the RHS has
a function return type with an effect row, extract and store that
row as the bound name's callable effect signature. Ensure this
works through let-chains (`let f = make(); let g = f`). Add
property tests verifying effects survive let-binding propagation.

**Note on `Fun(a, b)` vs `fn(a) -> b`:** The `Fun(a, b)` type
constructor doesn't carry effects. `fn(a) -[E]> b` does (the
parser already handles this via `FunctionWithEffect`). Users must
use the `fn` type syntax to express effectful function types.
Consider deprecating `Fun` in favor of `fn` type syntax.

### 5.1. Curried higher-order effect propagation — SOUNDNESS

**Reported by formal agent (720b4bd).** Related to §5 (phantom IO)
but a different code path. Effects are lost when a lambda returns
another lambda that calls its captured effectful argument.

**Reproduction (confirmed on latest MCP binary 2026-02-26):**

```kea
effect Log
  fn log(msg: Int) -> Unit

fn curried_test() -[Log]> Unit
  let apply = |f| -> |x| -> f(x)
  let logger = |y: Int| -> Log.log(y)
  apply(logger)(42)
```

- **Direct call:** `logger(42)` → `() -[Log]> ()` — correct
- **Curried call:** `apply(logger)(42)` → `() -[e0]> ()` — **bug**,
  effect variable `e0` not unified with `Log`

**Root cause (hypothesis):** When `apply` is inferred, its type is
roughly `(f: a -[e]> b) -> (x: a) -[e]> b`. The inner lambda
`|x| -> f(x)` captures `f` and calls it — `f`'s effect row `e`
should propagate to the inner lambda's effect row and then to the
outer call site. But the effect variable `e` appears to remain
unconstrained (`e0`) after `apply(logger)` is called, even though
`logger`'s concrete effect row `[Log]` should unify with `e`.

**Additional probes (2026-02-26, post-fix binary):**

- Annotated variant `|f: fn(Int) -[Log]> Unit|` gives error
  "the function is missing field `Log`" — the effect row in the
  `fn` type annotation is being fed into **record** row unification
  instead of **effect** row unification. This is a stronger signal
  than pure inference failure.
- Inline lambda application `(|f| -> |x| -> f(x))(logger)(42)`
  doesn't parse (separate issue, low priority).

**Likely location:** Two-part issue:

1. **Effect row in `fn` annotations treated as record row.** When
   a lambda parameter has an explicit `fn(a) -[E]> b` type
   annotation, the `[E]` effect row should unify with the caller's
   effect context. Instead it's being checked against the record
   row unifier, producing "missing field" errors. Check how
   `FunctionWithEffect` type annotations are lowered in
   `typeck.rs` — the effect row may be accidentally merged into
   the record row namespace.

2. **Unannotated curried case loses effect variable binding.**
   When `apply(logger)` is called, `logger`'s concrete `[Log]`
   effect should unify with `apply`'s effect variable `e`. The
   returned closure `|x| -> f(x)` should then carry `[Log]` as
   its effect. But `e` remains unconstrained (`e0`) — the
   unification of `logger`'s effect row with `apply`'s parameter
   type may not be reaching the effect variable in the returned
   closure's type.

**Fix approach:** The §5 fix (let-bound callable effect extraction)
is necessary but not sufficient. This also needs effect row
unification to fire correctly on `fn` type annotations in lambda
parameters, and for effect variables in curried return types to
be properly instantiated through application.

### 5.2. Effect row overlap not normalized — SOUNDNESS

**Reported by formal agent (33c3daa).** When a handler body emits
an effect that's already in the residual set, the effect row
contains duplicate labels instead of being deduplicated.

**Reproduction (confirmed on MCP 2026-02-26):**

```kea
effect Log
  fn log(msg: Int) -> Unit

effect Trace
  fn trace(msg: Int) -> Unit

fn body_fn() -[Log, Trace]> Unit
  Log.log(1)
  Trace.trace(2)

fn overlap_case() -[Trace]> Unit
  handle body_fn()
    Log.log(x) ->
      Trace.trace(x)
      resume()
```

Error: `declared effect [Trace] is too weak; body requires [Trace, Trace]`

**Expected:** Handler removes `Log` from `[Log, Trace]` → `[Trace]`.
Handler body adds `[Trace]`. Union should be idempotent per KERNEL
§5.4 ("commutative, idempotent set under union"): `[Trace] ∪ [Trace]`
= `[Trace]`. Instead the rows are concatenated → `[Trace, Trace]`.

**Root cause:** Effect row union in the handler typing rule
concatenates label lists without deduplication. The Rémy row
unification treats rows as ordered lists with a tail variable,
which naturally allows duplicates. Need a normalization pass after
handler effect removal + addition that merges duplicate labels.

**Fix:** After computing the handler result effect row
(`residual ∪ handler_body_effects`), normalize the closed portion
by deduplicating labels. For open rows (with tail variable), ensure
the "lacks" constraint prevents duplicates — a row variable `r`
that already has `Trace` in its concrete prefix should have
`lacks(r, Trace)` to prevent double-counting.

### 6. Inline if/then/else (KERNEL §10.4)

Block-style `if`/`else` works (indented branches). Inline form
`if x >= 0 then x else -x` does not parse. Low priority — block
style is idiomatic Kea — but the spec defines it and it's useful
for short expressions in `let` bindings.

### 7. Parametric type annotations in function params

Parametric ADT headers parse (`type Maybe a = Just(a) | Nothing`)
but applying parametric types in function parameter annotations
does not: `fn unwrap_or(opt: Maybe Int, default: Int) -> Int`
fails with a parse error at `Int` after `Maybe`. The parser sees
`Maybe` as the complete type and doesn't consume the type argument.

### 8. `Never` bottom type

KERNEL §5.2 specifies `fn fail(_ error: E) -> Never` but `Never`
is not a recognized type. Currently `Fail.fail` must return `Unit`,
which breaks control flow analysis — the type checker doesn't know
that code after `Fail.fail(e)` is unreachable. Needed for Fail to
work correctly as a diverging operation.

### 9. `catch` syntax

`catch expr` (KERNEL §5.8) desugars to a handler that wraps Fail
in Result. Parsing and codegen not yet wired. Low priority for 0d
(Fail compiles as Result-passing directly), but needed for
ergonomic error handling.

### 9.1. `catch` on Fail-absent body crashes — SOUNDNESS

**Reported by formal agent (c748717).** `catch expr` where `expr`
does not have `Fail` in its effect set produces "effect `Fail` has
no operation `fail`" error. Even `catch 42` fails. The desugaring
unconditionally references `Fail.fail` for the error handler clause
without checking whether `Fail` is in the body's effect set.

**Reproduction (confirmed on MCP 2026-02-27):**

```kea
effect Log
  fn log(msg: Int) -> Unit

fn pureish() -[Log]> Int
  Log.log(1)
  42

fn catch_absent() -[Log]> Int
  catch pureish()
-- ERROR: effect `Fail` has no operation `fail`
```

Even simpler: `catch 42` produces the same error.

**Expected:** `catch` on a Fail-absent expression should be a
compile error: "expression cannot fail; `catch` is unnecessary."
KERNEL §5.8 only defines `catch` for `{Fail E, R...}` — Fail
must be present. The implementation should check for Fail in the
body's effect set before desugaring.

**Secondary symptom:** The formal agent also observed that when
the error is worked around with permissive annotations, phantom
IO appears and Log gets dropped — likely downstream error recovery
injecting IO after the failed `Fail.fail` lookup.

### 10. Guard keyword: `when` vs KERNEL `if`

Implementation uses `when` for case guards; KERNEL §4.2.1 specifies
`if`. `when` is arguably better (no ambiguity with `if`/`else`
expressions). Reconcile: update KERNEL §4.2.1 to use `when`.

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

## Known Issues (pre-0d1)

Parser/typechecker/codegen gaps found during doc validation. These
were blockers for 0d1 stdlib ergonomics and compiled-path soundness;
all items below are now resolved (2026-02-26) and retained here as a
closeout record.

### Parser: function type annotations missing bare form

KERNEL §5 uses `A -[e]> B` for function type annotations in
parameters (e.g., `_ f: A -[e]> B`). This now parses directly on
type atoms (no mandatory `fn(...)` prefix), including both pure and
effectful arrow forms.

**Affected KERNEL signatures:**
- `fn map(_ self: List A, _ f: A -[e]> B) -[e]> List B` (§5.6)
- `fn retry(_ n: Int, _ f: () -[Fail E, e]> T) -[e]> Option T`
- `fn with_state(_ initial: S, _ f: () -[State S, e]> T) -[e]> (T, S)`

### Parser: effect row variable syntax

KERNEL uses comma before row variable: `-[Log, e]>`. Parser now
accepts both comma-tail (`-[Log, e]>`) and explicit pipe-tail
(`-[Log | e]>`) forms.

### Typechecker: Fail effect parameter not inferred

`Fail.fail("bad")` now infers `Fail String` (not bare `Fail`) in
effect rows by specializing Fail payload from call arguments in
effect-row inference.

### Codegen: direct constructor scrutinee dominance bug

`case Err(7)` previously failed codegen with a Cranelift verifier
dominance error (`uses value ... from non-dominating inst ...`) and
could also hit missing-value paths when defensive literal-case fallback
lowering dropped payload bindings.

Resolved by:
- restoring variable scope snapshots across MIR branch lowering
  (`if` and short-circuit control flow), preventing branch-local
  bindings from leaking into sibling blocks;
- lowering defensive literal-chain fallback through full arm binding
  logic (including constructor payload binds), not bare arm body.

## Progress
- 2026-02-26 17:03: Step 0 prerequisite slice landed in code: `FunctionType` now includes `effects: EffectRow` as structural type data; `Type` display/substitution/free-var traversal include function effects; infer/module env updates function type effects via `set_function_effect_row`; MCP now surfaces effectful function signatures via normal type display.
- 2026-02-26 17:03: Regression covered: phantom `IO` leakage in MCP declaration mode fixed by row-native declaration validation + MCP row-native effect plumbing.
- 2026-02-26 17:09: Step 1 scaffold landed: new `kea-hir` crate added with typed `HirModule/HirDecl/HirExpr` surface, lowering entrypoints (`lower_module`, `lower_function`), conservative raw-node fallback for unsupported syntax, and tests asserting bound function type/effect preservation.
- 2026-02-26 17:11: Step 2 scaffold landed: new `kea-mir` crate added with backend-neutral module/function/block model, explicit memory/effect/handler/call operation enums matching the 0d minimum MIR op contract, and a minimal HIR→MIR lowering stub with tests.
- 2026-02-26 17:14: Step 3 scaffold landed: new `kea-codegen` crate added with backend interface trait (`Backend`), ABI manifest artifact types, per-function pass stats collection, and a `CraneliftBackend` implementation stub that validates ABI coverage and consumes MIR.
- 2026-02-26 17:20: Step 2 lowering progressed from stub to real pure-path translation for `lit/var/binary/call/let/block`, with parameter binding and deterministic MIR return values plus regression tests for identity and arithmetic lowering.
- 2026-02-26 17:25: Step 3 backend progressed from stub to real Cranelift lowering for current pure MIR subset (`const`, `binary`, `call`, `return`) with host JIT compilation and AOT object emission paths covered by crate tests.
- 2026-02-26 17:29: Step 3 control-flow extension landed: Cranelift lowering now compiles multi-block MIR control flow with `Jump`/`Branch` terminators (no block params yet), unlocking incremental `if`/match lowering work.
- 2026-02-26 17:31: Step 2 control-flow extension landed: MIR lowering now emits block-graph control flow for Unit-typed `if` expressions (`Branch` + branch-local blocks + join), and the end-to-end `compile_hir_module` pipeline compiles this path.
- 2026-02-26 17:37: Step 2/3 control-flow value path landed: MIR blocks now carry typed block params and `Jump` arguments; non-Unit `if` lowers to join-block params; Cranelift lowering maps block params/args and compiles value-producing `if` end-to-end.
- 2026-02-26 18:03: Step 7 scaffold landed: new `crates/kea` CLI binary with `kea run <file>` and `kea build <file> [-o output|output.o]`, wired through parse/typecheck → HIR → MIR → codegen. `build` links executables by default (or emits `.o` when requested); `run` is now direct JIT entrypoint execution (no temporary object-link runner).
- 2026-02-26 17:51: Added CLI regression coverage in `crates/kea` tests: compile + execute a tiny Kea `main` function and assert exit-code propagation through the current run pipeline.
- 2026-02-26 17:51: Extended CLI regression coverage with bool-`case` execution path and direct-JIT run-path assertions for deterministic exit-code behavior.
- 2026-02-26 17:58: HIR `case` canonicalization extended: bool arms and literal (`Int`/`Bool`) arm chains with wildcard fallback lower to nested `if`; unsupported pattern classes still stay on the explicit non-lowered path until dedicated MIR case lowering lands.
- 2026-02-26 18:48: Benchmark lane advanced: `kea-bench` now includes string-transform-shaped and allocation-heavy workloads in addition to numeric baselines; repeated-run variance tooling (`bench:variance`) and CI artifact publication are in place for Stage B threshold calibration.
- 2026-02-26 18:53: Benchmark CI progressed to Step 2: `kea-bench` now builds through `codspeed-divan-compat`, and CodSpeed workflow wiring is in place for PR/main regression reporting once token configuration is enabled.
- 2026-02-26 18:56: Whole-program benchmark lane bootstrapped: added `benchmarks/programs/` corpus (`fib`, `case_chain`, `alloc_chain`) and `bench:programs` runner script (hyperfine + fallback path) to start collecting end-to-end `kea run` timing baselines.
- 2026-02-26 18:59: Microbenchmark matrix now includes type inference directly (`infer_numeric_module`) using the row-native inference pipeline, so Tier-1 benchmarks cover lex+parse+infer+lower+codegen for 0d.
- 2026-02-26 19:02: Stage B benchmark regression scaffold landed: seeded microbench baseline threshold file and non-blocking CI regression-check workflow with artifact publication (`bench:regression`) for threshold calibration before blocking gates.
- 2026-02-26 19:09: Whole-program regression scaffold landed: `bench:programs:regression` compares hyperfine means against seeded baseline thresholds, and non-blocking CI publishes program-regression summaries/artifacts for threshold calibration.
- 2026-02-26 19:10: Whole-program benchmark runner now measures multi-iteration command bodies (`BENCH_PROGRAM_INNER_ITERS`, default 10) through a no-shell execution path, reducing shell overhead/noise for fast programs and improving threshold signal quality.
- 2026-02-26 19:13: Whole-program variance tooling is now automated (`bench:programs:variance` + CI artifact workflow), giving threshold tuning an explicit spread/CV data source instead of one-off local runs.
- 2026-02-26 19:15: Non-blocking Stage B thresholds were tightened from initial bootstrap bands (`micro: 50%→35%`, `program: 60%→40%`) to increase regression signal while preserving calibration safety.
- 2026-02-26 17:57: Cranelift predicate normalization fixed for equality-driven control flow (`i8` vs `b1` predicate widths), with new codegen regression coverage for int equality branch conditions.
- 2026-02-26 17:48: Pure expression coverage expanded: unary operators (`-x`, `not x`) now lower HIR→MIR (`MirUnaryOp`) and compile through Cranelift, with targeted crate tests.
- 2026-02-26 17:50: HIR lowering now canonicalizes basic bool `case` expressions (`true/false/_` arms, no guards) into `if` expressions, allowing existing MIR/codegen control-flow lowering to compile that subset.
- 2026-02-26 18:04: Literal `case` coverage extended to include Float arms (`Int`/`Bool`/`Float` + wildcard fallback) via HIR canonicalization, with CLI execution regression for float-case dispatch.
- 2026-02-26 18:08: Literal `case` lowering now supports non-trivial scrutinee expressions by introducing a single-evaluation binding before the generated `if` chain (prevents per-arm re-evaluation), with HIR and CLI regressions.
- 2026-02-26 18:10: Literal `case` lowering now supports variable fallback arms (`n -> ...`) in addition to wildcard fallback, preserving single-evaluation scrutinee semantics and binding the fallback name explicitly in lowered HIR.
- 2026-02-26 18:22: Benchmark harness scaffold landed: new `kea-bench` crate with divan-based microbenchmarks (`lex+parse`, `HIR→MIR`, `HIR→JIT compile`) plus `mise run bench` task and recorded first local baseline output.
- 2026-02-26 18:43: Benchmark reporting infrastructure advanced: `scripts/bench-export.sh` now emits stable benchmark artifacts (`raw`, `summary.csv`, `summary.json`, `meta.json` with machine/context), and CI Stage A (`.github/workflows/bench-stage-a.yml`) runs + publishes artifacts on PR/push without regression fail gates.
- 2026-02-26 18:25: Boolean `and`/`or` now lower as short-circuit control flow in MIR (branch + join block), rather than eager bitwise-style evaluation, with MIR+codegen regression tests.
- 2026-02-26 18:28: HIR block lowering now propagates expected type hints to the block tail expression, allowing case/if tail desugaring to stay on the lowered path in typed contexts instead of falling back to raw nodes.
- 2026-02-26 18:33: Unit-enum constructor lowering landed for the pure path: zero-field constructors and qualified unit-constructor case patterns now lower through literal-tag comparisons (with exhaustive-case defensive else closure), enabling end-to-end execution of basic enum case programs.
- 2026-02-26 19:26: Pattern-matching coverage expanded for pure codegen path: OR-pattern literal/unit-enum case arms now lower through literal-chain canonicalization (instead of `Raw` fallback), with HIR regression tests plus end-to-end `kea` CLI execution tests (`Int` OR arms and unit-enum OR arms).
- 2026-02-26 20:01: Pattern-matching coverage extended for unqualified unit-enum constructor syntax: `case Red ...` and `Red | Green` pattern forms now remain on the lowered literal-tag path (same as qualified `Color.Red`), with HIR + CLI regressions.
- 2026-02-26 20:05: Pattern-matching coverage extended for `as` bindings on literal/unit-enum case arms (`0 as n`, `Color.Red as v`): lowered arms now insert explicit binding blocks on the compiled `if`-chain path instead of falling back to raw expressions, with HIR + CLI regressions.
- 2026-02-26 20:10: Pattern-matching coverage extended for guarded literal arms (`when`): literal/unit-enum `case` arms with guards now lower to short-circuit `and` conditions on the compiled `if` chain (with conservative fallback for guarded wildcard/var arms), with HIR + CLI regressions.
- 2026-02-26 20:11: Combined `as + when` literal-arm lowering now stays on the compiled path: guard evaluation binds the alias name before checking guard condition, then the arm body binds identically for expression scope; covered with HIR and end-to-end CLI regressions.
- 2026-02-26 20:15: Unit-enum guard coverage expanded on the lowered path (qualified constructor `when` and `as + when` forms), including expression-scrutinee block shape handling in HIR assertions and end-to-end CLI execution regressions.
- 2026-02-26 20:19: Case-lowering scrutinee setup optimized: if the lowered scrutinee is already a literal/var (including unit-enum constructor tags), avoid synthetic temp-binding blocks and emit direct `if` chains; added regression coverage for unit-enum scrutinee shape.
- 2026-02-26 20:22: Added explicit OR+guard regression coverage for both literal and unit-enum constructor arms (`0 | 1 when ...`, `Color.Red | Color.Green when ...`) in HIR and CLI tests to lock in combined condition lowering semantics.
- 2026-02-26 20:24: Guarded fallback arms now stay on the lowered literal-case path when an eventual fallback exists: supports `n when ...` and `_ when ...` fallback arms with correct ordering against later unconditional fallbacks, plus HIR/CLI regressions.
- 2026-02-26 20:28: OR-pattern aliasing widened: literal OR alternatives that bind the same `as` name (`0 as n | 1 as n`) now lower on the compiled path (including end-to-end CLI execution), while ambiguous mixed bindings still conservatively fallback.
- 2026-02-26 20:47: Parser gap slice landed for KERNEL alignment: `|...| ->` lambdas enabled (legacy `(x) ->` rejected), inline `if .. then .. else` enabled, parametric ADT headers and trait bare type params parse, and row type annotations (`{ name: String | r }`) parse; corpus snapshots and parser tests updated.
- 2026-02-26 20:47: Cranelift TCO slice landed for self-recursive tail calls: MIR tail-call detection now lowers to `return_call`, call-conv guarded for Apple AArch64 verifier constraints, and pass stats/regressions added for tail-self-call detection and release-prefix handling.
- 2026-02-26 20:47: Phantom IO effect leak on higher-order calls fixed: unknown callable effects now infer as open rows (not forced `[IO]`), recursive lookup can read function effects through `forall` wrappers, and regression coverage added to block reintroduction.
- 2026-02-26 21:25: Phantom IO closure-escape root cause fixed: let-bound call results now extract returned callable effect metadata from callee structural return types (`let f = make_emitter(); f(42)` preserves `Emit` instead of falling back to phantom `IO`), with new `kea-infer` and `kea-mcp` regression tests.
- 2026-02-27 03:37: Curried higher-order effect propagation fixed for both reported failure modes: (1) annotated callback params no longer fail with spurious "missing field `Log`" from pure-only call unification, and (2) unannotated curried callback application now propagates concrete argument effect rows through `|f| -> |x| -> f(x)` chains; added paired `kea-infer` regressions and MCP integration regression coverage.
- 2026-02-27 03:37: Parser call-syntax compatibility advanced for namespace qualification: lexer now tokenizes `::` (`ColonColon`), postfix parsing accepts `Module::fn(...)` alongside existing dot calls, and handler clause heads accept `Effect::op(...)`; added lexer + parser regressions (`List::map`, `Log::log(...)`) while preserving existing dot-form tests during transition.
- 2026-02-26 21:04: Backend-neutral layout side-table slice landed in MIR: `lower_hir_module` now extracts record field-order metadata and sum variant-tag metadata from raw HIR declarations into `MirLayoutCatalog`, with regression tests proving declaration-order preservation for record fields and enum variant tags.
- 2026-02-26 21:06: Codegen now validates MIR layout side-tables before backend lowering: duplicate type declarations, duplicate record fields, duplicate sum variants, and non-contiguous variant tags are rejected with explicit diagnostics, with targeted crate tests covering failure modes.
- 2026-02-26 21:39: Fail-only codegen invariant enforcement landed: `kea-codegen` now validates that `-[Fail E]>` functions never use generic handler ops/dispatch (`HandlerEnter`/`HandlerExit`/`Resume` or non-`ZeroResume` `EffectOp`) and fails compilation with a dedicated invariant diagnostic; regression tests cover accept/reject paths.
- 2026-02-26 21:42: Struct/enum lowering groundwork landed in backend ABI typing: nominal/structural record and sum carriers (`Record`, `AnonRecord`, `Sum`, plus `Option`/`Result`/`Opaque`) now lower to machine-word handles in Cranelift signatures, with regression tests proving record/sum-typed function signatures compile through the backend.
- 2026-02-26 21:43: Backend layout planning now materializes concrete record/sum memory-shape metadata (record field offsets, sum tag/payload offsets, max payload width, total size/alignment) from MIR layout catalogs during codegen preflight, with regression tests locking deterministic layout calculations.
- 2026-02-26 21:46: Pattern coverage expanded on the compiled path: bool `case` lowering now supports variable fallback arms (`true -> ...; b -> ...`) with correct scrutinee binding and single-evaluation setup for expression scrutinees, plus HIR and end-to-end CLI regressions.
- 2026-02-26 21:49: MIR layout catalogs now retain typed aggregate descriptors (record field annotations and per-variant sum field annotations), replacing name/count-only metadata and giving backend layout planning/lowering a typed substrate for upcoming struct/enum runtime lowering.
- 2026-02-27 04:33: Pattern coverage on the compiled path expanded for payload constructors: `as` bindings, compatible OR payload patterns (including across variants), guarded payload forms (`as + when`, `OR + when`), multi-payload binds (`Pair(a, b)`), and literal payload checks (`Yep(7)`, mixed literal+bind payloads), all with HIR and `kea` CLI regressions.
- 2026-02-27 04:33: Fail-only runtime lowering advanced: zero-resume `Fail.fail` now returns an allocated `Err(payload)` for Result-returning function signatures instead of always trapping; codegen now auto-imports `malloc` for this path, with a new JIT regression asserting `Err` tag/payload memory layout.
- 2026-02-27 04:33: End-to-end Fail Result-passing now propagates across local call boundaries in codegen: Fail-only functions use a runtime `Result` ABI, callers unwrap `Ok` payloads to continue computation, and `Err` short-circuits propagate to the current Fail-only frame; added JIT regressions for both Err propagation and Ok unwrap/re-wrap paths.
- 2026-02-27 04:42: Higher-order pure call path advanced on compiled backend: MIR now materializes top-level function references (`FunctionRef`) as first-class values, variable callees lower to `MirCallee::Value` for param calls, and Cranelift now lowers indirect `call_indirect` sites for function-pointer signatures (`Type::Function` as pointer ABI); added MIR regressions plus JIT end-to-end test (`run(41) == 43` through `apply_twice(inc, x)`).
- 2026-02-27 04:45: CLI end-to-end coverage now includes higher-order function-pointer execution from Kea source (`apply_twice(inc, 41) == 43`), closing the direct source-path regression gap for compiled pure HOF calls.
- 2026-02-27 04:51: Fail-only propagation now also works through indirect function-pointer calls: MIR call metadata marks fail-result ABI callees, Cranelift indirect calls reuse Result short-circuit plumbing, and new JIT regression asserts `Err(payload)` preservation through `FunctionRef` -> `call_indirect` -> failful target.
- 2026-02-27 04:55: Added lowering guard coverage for failful HOF metadata tagging (`callee_fail_result_abi`) in MIR and source-level CLI regression for local function aliases (`let g = inc; g(41)`), ensuring both alias and higher-order paths stay on the compiled backend without fallback.
- 2026-02-27 04:57: JIT entrypoint now supports Fail-only `main` ok-path execution (runtime `Result` ABI decode) and reports unhandled Fail on err-path; regression tests cover both behaviors while preserving existing pure `main` constraints.
- 2026-02-27 07:48: ABI lowering now treats `Unit` as a machine scalar (`I8`) in Cranelift type mapping so Fail payload/result layouts that normalize to `()` no longer hard-fail codegen.
- 2026-02-27 07:49: Added source-level CLI regressions for Fail-only `main` ok/err paths (with explicit `effect Fail` declaration), validating end-to-end parser→typeck→codegen entrypoint behavior beyond HIR-only unit tests.
- 2026-02-27 07:49: Pipe-language cleanup in inference diagnostics/tests: user-facing guidance now uses explicit call syntax (`Option.ok_or(opt, err)`), and infer property/test naming moved to neutral left-arg application terminology to keep no-pipe surface alignment.
- 2026-02-27 08:00: Struct/enum lowering depth increased on compiled path: payload constructors with non-literal fields now lower as structured HIR (`SumConstructor`) instead of raw AST fallback, MIR lowers them via `SumInit` with fully lowered field expressions, and new regressions cover `Yep(1 + 2)` through HIR, MIR, and end-to-end CLI execution.
- 2026-02-27 08:02: Benchmark gate baselines recalibrated from latest GitHub Actions artifacts (micro + program, non-blocking + stable classes) after large false-regression drift; threshold percentages remain unchanged, but baseline medians/means now reflect current `main` CI performance and threshold-check scripts validate with zero failures against the sampled artifacts.
- 2026-02-27 08:05: AOT coverage widened with compiled-binary execution regression (`kea build` path): added end-to-end test that compiles+links+runs enum/payload pattern code through object emission, and fixed macOS AOT linking for external runtime calls by enabling PIC/non-colocated libcalls in AOT ISA flags (`is_pic=true`, `use_colocated_libcalls=false`).
- 2026-02-27 08:34: Functional update compiled-path slice landed for record spread updates (`Record { ..base, field: value }`): HIR now lowers to `RecordUpdate`, MIR emits explicit memory-op sequence (`Retain`/`TryClaim`/`Freeze`/`CowUpdate`/`Release`), and codegen lowers `CowUpdate` by cloning unchanged fields + applying updated fields with layout metadata. Added HIR/MIR and end-to-end CLI regressions (`compile_and_execute_record_update_with_spread_exit_code`).
- 2026-02-27 09:05: CoW runtime path tightened: `CowUpdate` now performs a runtime uniqueness check (`refcount == 1`) and takes in-place mutation when unique, copy-allocate path otherwise. Aggregate allocations now include a refcount header, and `Result` allocation was migrated to the same heap-header layout so fail/result runtime handles remain consistent.
- 2026-02-27 09:07: Update-fusion slice landed for nested record-update chains: MIR lowering now flattens nested `RecordUpdate` bases into a single `CowUpdate` (preserving inner-to-outer evaluation order and last-write-wins per field), with dedicated MIR regression and end-to-end CLI regression for chained spread updates.
- 2026-02-27 09:27: Closed pre-0d1 parser/typeck blockers from doc validation: parser now accepts bare function type arrows in annotations (`A -> B`, `A -[e]> B`), parser accepts comma-tail effect row variables (`-[Log, e]>`), and effect inference now specializes `Fail` payload from call arguments (`Fail.fail("bad")` infers `Fail String`) with regression coverage in `kea-syntax` and `kea-infer`.
- 2026-02-27 09:27: Closed direct constructor-scrutinee compiled-path bug family: MIR branch lowering now snapshots/restores lexical var scope across branch paths (fixing non-dominating-value SSA leaks), and literal-case defensive fallback lowering now preserves payload bindings (`Err(e)` fallback no longer drops `e`), with HIR/MIR/CLI regressions including `case Err(7)` end-to-end.
- 2026-02-27 09:50: `catch` compiled-path support landed end-to-end on the Fail Result ABI path: HIR recognizes catch-desugared handles as structured `Catch`, MIR marks caught calls with fail-result capture metadata (no generic handler runtime), and codegen captures Result handles directly for case analysis. Fixed a runtime ABI soundness bug where declared effect contracts (for example `-[Fail E]>`) were validated but not persisted in function runtime metadata, which caused pure-inferred fail-declared callees to mismatch `catch` capture expectations and segfault. Added CLI regressions for both `catch` Err and `catch` Ok paths.
- 2026-02-27 10:04: String literal runtime lowering landed on the compiled path: Cranelift codegen now lowers `MirLiteral::String` by heap-allocating NUL-terminated bytes via the existing malloc-backed aggregate allocator and treating `String` as a pointer-handle ABI type (`I64`) in signatures/calls. Added `kea-codegen` regression `cranelift_backend_compiles_string_literal_module` and wired allocator detection so string-literal modules import malloc when needed.
- 2026-02-27 10:09: `IO::stdout` now runs on the compiled path: MIR lowers qualified `IO::stdout(...)` calls to `EffectOp { class: Direct, effect: IO, operation: stdout }`, and Cranelift lowers that op to an imported `puts` call (with string-literal heap pointers). Added MIR + codegen regressions and a CLI end-to-end test (`compile_and_execute_io_stdout_unit_main_exit_code`), establishing `hello world` execution (`fn main() -[IO]> Unit\n  IO::stdout("hello world")`) with JIT exit code `0`.
- 2026-02-27 10:13: Let-bound lambda calls now compile on the MIR path: local bindings of the shape `let f = |x| -> ...` are tracked as local lambda metadata and `f(args...)` is lowered by inlining the lambda body with argument bindings instead of emitting an unresolved local-function call. Added MIR regression (`lower_hir_module_inlines_let_bound_lambda_call`) and CLI end-to-end regression (`compile_and_execute_let_bound_lambda_call_exit_code`).
- 2026-02-27 10:21: Higher-order lambda literals passed as call arguments now compile (`apply(|x| -> x + 1, 41)`): MIR lambda lifting now resolves lambda function types from known callee signatures when HIR expression types are still `Dynamic`, synthesizes typed lifted lambda functions (`FunctionRef`) with stable names, and routes them through existing indirect-call lowering. Added CLI regression `compile_and_execute_higher_order_lambda_argument_exit_code`.
- 2026-02-27 10:33: Direct lambda-call expressions now compile on the MIR path (`(|x| -> x + 1)(41)`): `lower_call_expr` now inlines lambda-callee calls by binding parameters to lowered argument values in lexical scope and lowering the lambda body directly, avoiding dynamic function-ref fallback for this form. Added MIR regression `lower_hir_module_inlines_direct_lambda_call` and CLI regression `compile_and_execute_direct_lambda_call_exit_code`.
- 2026-02-27 10:37: Added source-level TCO regression coverage with deep self-tail recursion (`count(100000, 0)`): CLI test `compile_and_execute_tail_recursive_countdown_exit_code` validates compiled-path execution for large tail-recursive depth, complementing existing MIR/codegen tail-call detection/unit tests.
- 2026-02-27 10:38: Row-polymorphic record field access now stays on the compiled path for concrete carriers (`fn get_age(u: { age: Int | r }) -> Int` with `User` call sites): MIR lowering now resolves `Type::AnonRecord` field loads/binds to a unique concrete record layout from the layout catalog when one unambiguous carrier matches the required field set, preventing missing-return/unsupported-op fallbacks. Added MIR regression `lower_hir_module_resolves_record_field_load_for_anon_record_param` and source-level CLI regression `compile_and_execute_row_polymorphic_record_field_access_exit_code`.
- 2026-02-27 10:43: Capturing-lambda factory calls now stay on the compiled path for common pure patterns (`fn make_adder(y) -> fn(Int) -> Int; let f = make_adder(2); f(40)` and immediate call forms): MIR now detects function-returned lambda factories, binds capture arguments at call sites, and inlines the resulting local lambda body instead of emitting unresolved closure-pointer runtime paths. Lifted lambda lowering now includes in-scope captures as explicit leading parameters so generated helper functions compile deterministically even when closure conversion is deferred. Added MIR regression `lower_hir_module_inlines_let_bound_lambda_from_factory_call` and CLI regression `compile_and_execute_returned_capturing_lambda_call_exit_code`.
- 2026-02-27 10:45: Added explicit source-level regression for immediate capturing factory calls (`make_adder(2)(40)`) via `compile_and_execute_immediate_capturing_lambda_call_exit_code`, locking the direct call-chain lowering path alongside the let-bound factory-call path.
- 2026-02-27 10:47: Phantom IO leak fixed in handle-expression effect inference: when a `handle` expression handles an effect NOT present in the body's closed effect row (mismatched handler), the row decomposition constraint was unsatisfiable and fell back to IO. Fix adds early return in the Handle arm of `infer_expr_effect_row` that passes body effects through unchanged when the handled effect is absent. Regression tests cover both directions (body=Log/handler=Trace and body=Trace/handler=Log). Commits: 746a4cb (fix), 9812380 (tests).
- 2026-02-27 10:54: Closed a silent wrong-code path for escaping capturing closures (`apply(make_adder(2), 40)` previously returned `80` from function-pointer ABI/signature mismatch). MIR now emits an explicit `Unsupported` instruction for escaping capturing-factory values (anything outside immediate call or let-bound invocation), and codegen reports a compile-time `UnsupportedMir` error instead of miscompiling. Added CLI regression `compile_and_execute_escaping_capturing_lambda_value_is_rejected` while keeping supported let-bound/immediate factory invocation paths green.
- 2026-02-27 11:00: Dot-call method syntax now follows CALL-SYNTAX expectations on compiled path: parser desugars value-method calls `x.method(a, b)` to `method(x, a, b)` while preserving qualified module/trait access forms (`List::map(...)`, explicit field-access chains). Added parser regressions for receiver-first desugaring and a source-level CLI regression `compile_and_execute_dot_method_dispatch_exit_code`. MIR field-access lowering now also recovers nominal record layouts from call-return function signatures so chained forms like `user.inc().age` stay on compiled path (no missing-return fallback).
- 2026-02-27 11:03: Added MIR regression lock-in for recent call/lambda safety fixes: `lower_hir_module_resolves_record_field_load_for_call_result_var_type` guards call-result record-layout recovery, and `lower_hir_module_marks_escaping_capturing_factory_call_unsupported` guards explicit unsupported-lowering for escaping capturing factory values (no silent wrong-code regression).
- 2026-02-27 11:05: Dot-dispatch desugaring now covers field-access receivers (for example `wrapped.inner.inc()`), while still preserving trait-qualified chains by keeping uppercase receiver-segment paths out of receiver-first rewrite. Added parser regression `parse_dot_call_with_field_access_receiver_desugars` and CLI regression `compile_and_execute_dot_method_dispatch_on_field_access_receiver_exit_code`.
- 2026-02-27 11:12: Added compiled-path runtime lowering for `String ++ String` in Cranelift: `MirBinaryOp::Concat` now lowers via libc `strlen`/`memcpy` plus dynamic heap allocation (refcount-header-compatible payload) instead of hitting unsupported binary-op diagnostics. Added `kea-codegen` regression `cranelift_backend_compiles_string_concat_stdout_module`. Note: source-level `++` for `String` is still inference-gated (`Concatenable` trait coverage), so end-to-end Kea CLI concat tests remain pending infer-side enablement.
- 2026-02-27 11:15: Closed the source-level concat gate in inference: `check_expr_bidir` now accepts built-in concatenable carriers (`String`, `List`, `Seq`) for `++` when trait registry evidence is absent, so typed call-argument checking no longer rejects `String` concat. Added infer regressions (`infer_concat_strings`, `infer_concat_string_argument_to_typed_call`) and re-enabled CLI regression `compile_and_execute_io_stdout_string_concat_exit_code` to lock parser→infer→MIR→codegen execution for `IO::stdout("hello " ++ "world")`.
- 2026-02-27 11:20: Named-variant payload labels now stay correct on compiled paths: HIR constructor lowering reorders labeled constructor args by declared variant field names (instead of call-site order), and literal-case constructor pattern lowering now supports named payload patterns (`Pair(left: a, right: b)`) by mapping labels to payload slots. Added HIR regression `lower_function_named_payload_constructor_reorders_labeled_args` and source-level CLI regression `compile_and_execute_named_payload_constructor_labeled_args_exit_code`.
- 2026-02-27 11:23: Qualified payload constructors now lower directly to structured sum initialization on compiled paths: HIR recognizes `Type.Variant(args...)` call shape as constructor initialization (instead of generic function call), including labeled payload reordering through declared variant field names. Added HIR regression `lower_function_qualified_payload_constructor_stays_structured_hir` and source-level CLI regression `compile_and_execute_qualified_payload_constructor_case_exit_code` (`case Flag.Yep(7)` / `Flag.Yep(n)`).
- 2026-02-27 11:27: AOT runtime determinism tightened for exported `main`: Unit-returning `main` now lowers to an explicit `i32` return of `0` (instead of relying on implicit register state), fixing flaky/incorrect nonzero exits on effectful Unit mains (`IO::stdout(...)`) in native binaries. `execute_hir_main_jit` updated to match the new Unit-main runtime signature (`extern "C" fn() -> i32`).
- 2026-02-27 11:27: AOT CLI regression coverage widened and stabilized: added end-to-end `kea build` tests for effectful Unit mains (`compile_build_and_execute_aot_io_stdout_unit_main_exit_code`, `compile_build_and_execute_aot_io_stdout_concat_exit_code`) and fixed temporary object-path collisions in `link_object_bytes` by using unique per-link temp filenames (timestamp + nonce), preventing parallel-test cross-link contamination.
- 2026-02-27 11:29: Exported `main` ABI normalized for both `Int` and `Unit`: codegen now always emits `i32` return type for non-fail AOT/JIT entrypoints, with explicit coercion on Int return paths. This removes reliance on host ABI widening/truncation for `i64` Int mains and keeps exit-code semantics deterministic across JIT and native binaries.
- 2026-02-27 11:38: Closed the record-pattern `case` compiled-path gap for named records: HIR now lowers `case` arms like `User { age: 4, .. }` to structured `if` chains with field checks/binds (instead of raw fallback), preserving single-evaluation scrutinee setup and guarded/fallback arm semantics. Added HIR regression `lower_function_record_pattern_case_desugars_to_if_chain` and CLI regression `compile_and_execute_record_pattern_case_exit_code`, eliminating the previous `unsupported MIR operation ... non-unit function returned without value` failure for this path.
- 2026-02-27 11:43: Extended compiled-path record-pattern coverage to anonymous record patterns on concrete carriers: HIR record-case lowering now accepts `#{ ... }` pattern arms (including OR/`as` compatibility checks) and lowers them through the same structured field-check/field-bind path as named record patterns. Added HIR regression `lower_function_anon_record_pattern_case_desugars_to_if_chain` and source-level CLI regression `compile_and_execute_anon_record_pattern_case_exit_code` (matching `#{ age: 4, .. }` against a concrete `User` scrutinee).
- 2026-02-27 11:45: Locked both record-field pattern binding shapes from KERNEL §4.2 on the compiled path: explicit rename bindings (`User { age: years, .. }`) and pun bindings (`User { age, .. }`) now have dedicated regressions. Added HIR binding-shape test `lower_function_record_pattern_field_binding_uses_field_access` plus source-level CLI regressions `compile_and_execute_record_pattern_renamed_field_binding_exit_code` and `compile_and_execute_record_pattern_pun_binding_exit_code`.
- 2026-02-27 11:47: Added guard-binding coverage for record destructuring on compiled path: record-pattern `when` guards now have explicit regression lock-in showing bound field names are introduced before guard evaluation (HIR test `lower_function_record_pattern_guard_binds_before_guard`) and execute correctly end-to-end (`compile_and_execute_record_pattern_guard_binding_exit_code`).
- 2026-02-27 11:51: Closed OR-record-pattern lowering gap on compiled path: `User { age: 3, .. } | User { age: 4, .. }` now lowers as multiple compatible record arms (same bind sites, differing literal checks) instead of falling back to raw/unsupported MIR. Added HIR regression `lower_function_record_pattern_or_literals_desugar_to_if_chain` and CLI regression `compile_and_execute_record_pattern_or_literal_exit_code`.
- 2026-02-27 11:57: Landed compiled-path runtime support for anonymous record literals with synthetic MIR layouts: lowering now seeds deterministic layout entries for raw `#{ ... }` literals, lowers raw anon-record construction to `RecordInit`, and tracks runtime record-type metadata through let-bindings so subsequent field loads/case destructuring stay on structured MIR. Added MIR regressions (`lower_hir_module_seeds_synthetic_layout_for_raw_anon_record_literal`, `lower_hir_module_lowers_raw_anon_record_literal_field_access_expression`) and source-level CLI regressions (`compile_and_execute_anon_record_literal_field_access_exit_code`, anon-record pattern case now uses anon literal scrutinee directly).
- 2026-02-27 11:59: Added explicit end-to-end regression for anon-record OR pattern matching on compiled path (`#{ age: 3, .. } | #{ age: 4, .. }`) via `compile_and_execute_anon_record_pattern_or_literal_exit_code`, guarding the combined synthetic-layout + OR-arm lowering path.
- **Note for codegen agent:** The phantom IO leak fix (746a4cb) is purely in `kea-infer` effect inference. No codegen changes needed. The fix ensures that mismatched handle expressions (handler handles an effect the body doesn't perform) correctly preserve the body's actual effects instead of introducing phantom IO. This means codegen can trust that effect rows on handle expressions are accurate — if IO shows up, it's real IO, not an inference artifact. No action required on your end.
- **Next:** Continue the remaining 0d runtime/codegen delta by expanding struct/enum runtime lowering beyond handle-only carriers and tightening remaining compiled-path coverage for effects/handlers without regressing current pure + Fail-only fast paths.
