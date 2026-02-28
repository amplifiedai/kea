# Brief: Self-Hosting Compiler Performance Strategy

**Status:** design
**Priority:** v1
**Depends on:** 0f (memory model), 0g (advanced types), Phase 1 (self-hosting)
**Blocks:** nothing (design doc, informs implementation)
**Also read:**
- [COMPILER-AS-DATA](../../docs/COMPILER-AS-DATA.md) — the architectural thesis
- [0f-memory-model](../in-progress/0f-memory-model.md) — Step 3 memory optimisation pipeline
- [performance-backend-strategy](performance-backend-strategy.md) — MIR/backend design

## Overview

This brief covers five interconnected ideas:

1. **Language-level wins** (§Unique Pipeline through §Compound Advantage) — how Kea's type system and effect system deliver zero-RC pipelines, parallel compilation, arenas, and incremental queries.
2. **Kea-native backend** (§Phase 2-3) — 10 categories of optimisation that general-purpose backends can't perform, plus memory layout, whole-program analysis, and numeric tiers.
3. **Static PGO** (§Static PGO) — the type system provides most of what traditional PGO discovers at runtime; runtime profiling via the `Profile` effect covers the rest.
4. **Bootstrapping acceleration** (§Bootstrapping Acceleration) — each self-hosted generation is a better optimiser running on optimisation-amenable code.
5. **Concrete gates** (§Acceptance Gates) — measurable criteria for Phase 1, 2, and 3.

All performance claims in this brief are **architectural ceilings to validate**, not promises. Absolute numbers require benchmark gates (see performance-backend-strategy.md). Estimated impacts are directional, not commitments.

## Motivation

The self-hosted Kea compiler is the language's flagship program. If Kea
claims to produce fast functional code, the compiler must be fast. But
more than that: a compiler is the *perfect* workload for Kea's memory
model. The techniques in 0f (Perceus reuse, auto borrow, TRMC, FIP)
combine with Unique T and the effect system to produce a compiler that
is structurally faster than what other approaches can achieve.

This brief captures why and how, so the self-hosting effort is guided
by performance from the start — not optimised after the fact.

## The Competitive Landscape

Nobody has shipped a general-purpose functional language with
Perceus-class RC optimisations and production tooling.

| Language | Has the algorithms | Has the tooling | Production-ready |
|----------|-------------------|-----------------|-----------------|
| Koka | Yes | No (no pkg mgr, minimal stdlib, compiler bugs on complex effects) | No |
| Lean 4 | Mostly | Yes | For proofs, not general SW |
| Roc | Not yet | Not yet | No |
| Swift | Partially (naive ARC, no reuse) | Yes | Yes, but not functional |
| OCaml | No (GC) | Yes | Yes, but GC-bound |

The published Perceus benchmarks show 2-4x over Swift's ARC on tree
operations (rbtree: Koka 1.0x vs Swift ~2.45x). Swift can't add reuse
analysis without redesigning ARC — their mutable-object-with-identity
memory model prevents it. Kea's immutable-by-default semantics are
what enable these optimisations. Functional = faster on these workloads.

## Why Compilers Are the Perfect Workload

A compiler is:
1. Parse source → build tree
2. Transform tree → new tree (5-10 passes)
3. Emit output → discard trees

Every pass is a pattern match + reconstruct. That's exactly where
Perceus reuse analysis gives zero-allocation in-place updates. A
constant-folding pass, a desugaring pass, a dead-code pass — when the
IR is uniquely owned, every one runs with zero heap allocation.

Lean 4 validates this. Their self-hosted compiler uses RC + destructive
updates on unique values and spends only 17% of runtime on deallocation
vs OCaml's 90% in GC.

## The Unique Pipeline

The COMPILER-AS-DATA pipeline is linear:

```
Source -[Parse]> AST -[TypeCheck, Diagnose]> HIR -[Lower]> MIR -[Lower]> Target
```

Each IR flows forward through one owner. Type the pipeline with Unique:

```kea
fn parse(_ src: String) -> Unique Ast -[Parse, Diagnose]>
fn infer(_ ast: Unique Ast) -> Unique TypedAst -[TypeCheck, Diagnose]>
fn lower(_ typed: Unique TypedAst) -> Unique MirExpr -[Lower]>
fn optimize(_ mir: Unique MirExpr) -> Unique MirExpr   -- pure!
fn codegen(_ mir: Unique MirExpr) -> Bytes -[Codegen]>
```

The primary IR flow through this pipeline has **zero RC overhead**. No
increments, no decrements, no COW checks, no atomic operations. Each
transformation is guaranteed in-place. Shared compiler state — symbol
tables, type interning caches, imported module signatures — remains
refcounted or behind borrow, since multiple passes read it. But the
primary data (the IR being transformed) flows linearly with no RC cost.

## Arena Allocation via Alloc Effect

Compilers are the canonical arena use case:

```kea
fn compile_file(_ src: String) -> Bytes
  handle parse(src) with
    Alloc -> Arena.new(4096)   -- bump allocator for this phase
  -- arena freed here, all AST nodes gone at once
```

Unique T inside `-[Alloc]>` is the strongest path: zero RC checks
(Unique) + bump allocation (Alloc) + unconditional in-place updates.
For the parse phase — hundreds of thousands of AST nodes discarded
after lowering — arenas give 2-5x over general-purpose allocation
from cache locality alone.

## Type-Proven Parallel Compilation

The compilation DAG has natural parallelism at every level:

```
Phase 1: Parse        — embarrassingly parallel (per file)
Phase 2: Import DAG   — sequential but cheap (topological sort)
Phase 3: Type check   — parallel per module (topo order), parallel per function within
Phase 4: Lower        — parallel per module (after types resolved)
Phase 5: Optimize     — embarrassingly parallel per function (PURE)
Phase 6: Codegen      — embarrassingly parallel per function
```

Three Kea features compound to make this zero-cost and type-checked:

**1. Unique T = zero-cost task handoff.** When a parse task produces
`Unique Ast`, sending it to the type-check task is a move. No cloning,
no atomic RC, no shared state. The AST literally moves between tasks.

**2. Pure passes = safe Par.** The optimise pass is `->` (pure). The
effect system *proves* it's safe to run in parallel — no locks, no
synchronisation, because the types prove there's nothing to synchronise
over.

**3. Par.map at function granularity.** Not per-translation-unit (gcc)
or per-codegen-unit (rustc). Per function. Because effects prove purity
and Unique proves non-aliasing at the function level.

The full parallel pipeline:

```kea
fn compile_project(_ files: List String) -> List Bytes -[Spawn, IO]>
  -- Phase 1: parse all files in parallel
  let asts = Par.map(files, |path|
    parse(read_file(path))        -- each returns Unique Ast
  )

  -- Phase 2: build import DAG, topological sort
  let order = resolve_imports(asts)

  -- Phase 3-4: type check + lower in dependency order
  -- modules in the same topo level compile in parallel
  let mirs = order.levels.flat_map(|level|
    Par.map(level, |module|
      lower(infer(module))        -- Unique flows through
    )
  )

  -- Phase 5: optimize all functions across all modules (PURE)
  let optimized = Par.map(mirs, |mir|
    let fns = Par.map(mir.functions, |fn_body|
      constant_fold(fn_body)
        .then(dead_code_eliminate)
        .then(inline_small)
    )
    mir~{ functions: fns }
  )

  -- Phase 6: codegen all functions in parallel
  Par.map(optimized, codegen)
```

Every `Par.map` is type-checked safe. The effect signatures prove
which phases are pure. The Unique types prove the data doesn't alias.
The functional updates (`mir~{ functions: fns }`) are in-place when
the input is unique (reuse analysis). No engineering discipline
required — the compiler rejects unsafe parallelism at compile time.

**Comparison with existing compilers:**

| | rustc | gcc | Go | Kea |
|---|---|---|---|---|
| Parse | Sequential | Sequential | Parallel (per file) | Par (per file) |
| Type check | Sequential | Sequential | Parallel (per pkg) | Par (per topo level, per fn within) |
| Optimise | Sequential per CGU | Parallel per TU | Sequential | Par (per function, proven pure) |
| Codegen | Parallel per CGU | Parallel per TU | Parallel | Par (per function) |
| Safety proof | Engineering | Engineering | Engineering | Effect system + Unique T |
| Data handoff | Arc/shared memory | Shared memory | Channels | Unique move (zero-cost) |

Rustc parallelises codegen but not type checking. GCC parallelises
across translation units but not within them. Go parallelises per
package but uses a shared mutable symbol table with locks.

Kea parallelises at the *function* granularity because the effect
system proves which passes are pure and Unique T proves the data
doesn't alias. This is the same insight that makes Sorbet fast (100K
lines/sec/core for pure per-method type inference), but with a
type-level guarantee instead of engineering discipline.

## Incremental Compilation via Query Effects

The COMPILER-AS-DATA architecture maps naturally to Salsa-style
incremental computation:

```kea
effect Query
  fn input(_ key: FileId) -> Source
  fn memo(_ key: QueryKey) -> Result

fn typecheck(_ file: FileId) -> Types -[Query, Diagnose]>
  let src = input(file)                    -- tracked dependency
  let ast = memo(ParseQuery(file))         -- cached if source unchanged
  let types = memo(InferQuery(ast))        -- early cutoff if AST unchanged
  types
```

Content-addressed hashing on immutable IR nodes gives early cutoff for
free: if a whitespace-only edit doesn't change the AST hash, all
downstream passes are skipped. Rust-analyzer's Salsa framework does
this with manual annotations. In Kea, the effect system *is* the
annotation — `Query` effect = tracked dependency.

## The Compound Advantage

No single technique is unique to Kea. But nobody has all of them
together, and nobody has an effect system that unifies them:

| Technique | Who has it | Kea's edge |
|-----------|-----------|------------|
| Reuse analysis | Koka, Lean | Unique T proves it statically, no runtime check |
| Borrow inference | Lean | Effects give more information (pure = nothing escapes) |
| TRMC | Koka | Native backend compiles TRMC hole-pointer as register-resident write cursor (C-speed map from functional source) |
| Parallel compilation | Sorbet (per-method), Go (per-pkg) | Par per function with type-level safety proof (effects + Unique) |
| Arena allocation | Every C compiler | Alloc effect makes it composable and safe |
| Incremental queries | rust-analyzer | Query effect tracks dependencies in the type system |
| Zero-RC IR pipeline | Nobody | Unique T through linear pipeline eliminates RC entirely |
| Non-aliasing for vectorisation | C (`restrict`), Rust (borrow checker) | `Unique (Array T)` = type-level proof, enables auto-vectorisation without annotation |

## Runtime Performance: All Programs, Not Just the Compiler

The techniques above apply to the compiler because it's a Kea program.
But they apply to *every* Kea program. The self-hosting compiler is the
showcase, not the only beneficiary.

- A user writing a red-black tree gets zero-allocation insertions (reuse)
- A user writing parser combinators gets TRMC'd recursive descent (loop)
- A user writing a web server gets arena-scoped request handling (Alloc)
- A user writing a data pipeline gets closure devirtualisation (map/filter)
- A user writing concurrent code gets zero-cost task handoff (Unique move)

The Perceus benchmarks (2-4x over Swift on tree ops) apply to all Kea
programs. The effect handler compilation classes apply to all effectful
code. The closure devirtualisation applies to all higher-order code.

With a Kea-native backend (Phase 2-3), the architectural ceiling is:
**match or beat LLVM -O2 for Kea-idiomatic code** (functional data
structures, effect-heavy control flow, closure-heavy higher-order code)
while compiling significantly faster. This is a hypothesis to validate
with benchmarks, not a promise. Tight numeric loops will still lose to
LLVM, but that's not what Kea programs look like.

## Performance Targets

| Dimension | Target | Basis |
|-----------|--------|-------|
| IR pass throughput | Zero-allocation (reuse + Unique) | Perceus benchmarks, Lean validation |
| Memory management overhead | <20% of runtime | Lean's 17% vs OCaml's 90% |
| Codegen speed (Phase 0-1) | Cranelift: 20-40% faster than LLVM | Cranelift 2024 benchmarks |
| Codegen speed (Phase 2 debug) | Hypothesis: 10-100x faster than LLVM | Copy-and-patch / minimal opt |
| Code quality (Phase 2 release) | Hypothesis: match LLVM -O2 on functional patterns | Domain-specific optimisations |
| Type checking throughput | 100K+ lines/sec/core | Sorbet architecture |
| Parallel scaling | 2-4x on 4+ cores | Sorbet, rustc codegen |
| List/tree traversal (TRMC+reuse) | Within 2x of hand-written C loop | Koka FBIP benchmarks, item 9 |
| Incremental rebuilds | Sub-100ms for single-file edits | Salsa-style early cutoff |
| FFI trampoline overhead | <5ns per C call | Go/OCaml calling convention transition cost |

## What This Means for Self-Hosting

The compiler is just a Kea program. It gets all the same optimisations
any Kea program gets:
- Pure passes get better RC elision (auto borrow inference)
- Unique IR nodes get zero RC (no runtime checks)
- Arena-scoped phases get bump allocation
- Structure-preserving passes get reuse tokens (FBIP)
- List/tree traversals get TRMC (loop, not recursion)

And because the compiler's passes declare their effects, the compiler
can optimise itself — it is simultaneously the optimiser and the
program being optimised.

The architectural target: **competitive with OCaml's compilation speed**
while offering a richer type system (effects, row polymorphism, Unique).
Whether this reaches "one of the fastest functional language compilers"
is an empirical question gated on benchmarks — but the structural
advantages (the language's own features are what a compiler optimiser
wants to reason about) give strong reason to expect it.

## Phase 2-3: Kea-Native Backend Strategy

Cranelift is the right Phase 0-1 backend: fast compilation, good enough
code quality, battle-tested. But general-purpose backends are blind to
Kea's semantics. A Kea-native backend — written in Kea, for Kea — can
exploit information that Cranelift and LLVM structurally cannot see.

### What General-Purpose Backends Can't See

Cranelift sees function calls. It doesn't know that:

1. **RC operations are semantic, not opaque.** `retain(x); release(x)`
   is a no-op. `release(x); alloc(sizeof(x))` can reuse `x`'s memory.
   Cranelift sees two unrelated function calls.

2. **Closures have known structure.** A closure capturing `[x, y]` with
   body `fn(z) -> x + y + z` could be inlined at the call site if the
   closure is unique. Cranelift sees an indirect call through a function
   pointer.

3. **Effect handlers have dispatch semantics.** A tail-resumptive handler
   is equivalent to a direct call. A zero-resume handler (Fail) is
   equivalent to `setjmp/longjmp`. Cranelift sees generic call/return
   through evidence tables.

4. **Pattern matches have exhaustive structure.** A match on `Option T`
   always has exactly two branches. Cranelift sees a switch on an integer
   tag.

5. **Allocations have effect-scoped lifetimes.** Inside an `Alloc`
   handler, all allocations are bump-allocated and freed at handler exit.
   Cranelift sees individual `malloc` calls.

### What a Kea-Native Backend Enables

Eight categories of optimisation, each compounding with the others:

**1. RC Coalescing and Sinking**

```
retain(x)          -- Kea backend sees: net effect = 0
use(x)             -- eliminates both retain and release
release(x)
```

Move `release` to the last use point. Fuse `retain; release` pairs.
Propagate RC across basic blocks. A general backend can't touch these
because it doesn't know `retain`/`release` are inverses.

*Estimated impact:* 10-30% fewer RC operations beyond what Perceus gives.

**2. RC Uniqueness Propagation**

When a value is statically Unique, all RC operations on it are dead code.
When a value *becomes* unique (refcount drops to 1), the backend can
switch downstream operations to the unique fast path.

```kea
-- static: x is Unique, no RC emitted at all
-- dynamic: after release drops rc to 1, subsequent ops use in-place path
```

*Estimated impact:* 5-15% on programs with mixed unique/shared values.

**3. Closure Devirtualisation**

When a closure's allocation site is visible and it flows to a single
call site (common in `map`, `filter`, `fold`), inline the closure body:

```
-- before: indirect call through closure env
let f = |x| x + captured_y
xs.map(f)

-- after: direct inline at call site
xs.map_inlined(|x| x + captured_y)
```

This is the optimisation that makes `xs.map(|x| x + 1)` as fast as a
hand-written loop. LLVM can sometimes do this; Cranelift cannot.

*Estimated impact:* 15-40% on higher-order-function-heavy code (most Kea code).

**4. Effect Handler Compilation Classes**

Classify handlers at compile time and emit specialised code:

| Handler class | Compilation strategy |
|---|---|
| Tail-resumptive (Log, State) | Direct call, no stack manipulation |
| Zero-resume (Fail) | setjmp/longjmp or return-code propagation |
| Multi-shot (Amb, backtrack) | Full continuation capture (rare) |
| Capability-only (IO boundary) | Evidence passing, no dispatch |

Tail-resumptive handlers are ~80% of handlers in practice. Compiling
them as direct calls eliminates the evidence-table dispatch overhead
entirely. Cranelift sees all handlers uniformly.

*Estimated impact:* 20-50% on effectful code (most Kea code).

**5. Inline Bump Allocation**

Inside an `Alloc` handler scope, replace `malloc` with a pointer bump:

```asm
; instead of: call malloc
mov rax, [arena_ptr]       ; load bump pointer
add [arena_ptr], size      ; bump
; done — no free list, no headers, no fragmentation
```

Three instructions instead of a function call. All deallocations
happen at handler exit as a single pointer reset.

*Estimated impact:* 2-5x on allocation-heavy phases (parsing, lowering).

**6. Custom Calling Convention**

Kea-native functions don't need the C calling convention:

- Pass effect evidence in dedicated registers (no stack spills)
- Return small structs in registers (no alloca for Result/Option)
- Tail calls guaranteed (not "best effort" like Cranelift)
- Closure env pointer in a fixed register

Trade-off: C FFI calls need a trampoline to transition between Kea's
calling convention and SysV/Win64. Go and OCaml pay this cost (~2-5ns
per transition). For Kea-to-Kea calls (the vast majority), the custom
convention is pure upside.

*Estimated impact:* 5-15% from reduced calling overhead.

**7. Pattern Match Optimisation**

With full knowledge of enum layouts and exhaustiveness:

- Bit-test switches for small enums (Option, Result, Bool)
- Jump tables with guaranteed coverage (no default branch)
- Nested match flattening (match on `Option (List T)` → single switch)
- Tag-in-pointer encoding for single-field variants

*Estimated impact:* 5-10% on pattern-match-heavy code (compiler passes).

**8. Reuse-Aware Register Allocation**

When reuse analysis proves an allocation reuses a drop's memory, the
backend can keep the memory location in a register across the
"drop + alloc" boundary — the pointer never touches the stack.

*Estimated impact:* 5-10% on tree-transforming code.

**9. TRMC as a Tight Write-Cursor Loop**

TRMC (Tail Recursion Modulo Context) transforms `map` from stack
recursion into a loop that fills "holes" — placeholder slots in
partially-constructed list nodes. The MIR-level TRMC transformation
is backend-agnostic. But a Kea-native backend can compile the hole
pointer as a register-resident write cursor:

```
; map(xs, f) compiled with TRMC + reuse + native backend:
loop:
  test [xs], tag_nil          ; is xs Nil?
  je done
  mov head, [xs + head_off]   ; load head
  mov next, [xs + tail_off]   ; load tail BEFORE overwriting (reuse!)
  call f, head                ; apply f (or inline if known)
  mov [xs + head_off], result ; overwrite head in-place (reuse token)
  mov [cursor], xs            ; link reused node into output list
  lea cursor, [xs + tail_off] ; advance cursor to next hole
  mov xs, next                ; advance input (from saved tail)
  jmp loop
```

TRMC + reuse (the input node is recycled as the output node) + native
backend (cursor in register, known struct offsets) = `map` as a tight
loop that mutates list nodes in-place. **C-speed `map` from functional
source code.** Cranelift can't do this because it doesn't know the
list node layout or the TRMC hole semantics.

*Estimated impact:* 30-50% on list/tree traversals (map, filter, flatMap).

**10. Backend-Level Escape Analysis**

The MIR-level escape analysis (pure scope → stack allocate) is a
coarse pass. A Kea-native backend can do finer escape analysis with
more information: if a closure is created, passed to a known call,
and never stored, stack-allocate the closure environment. The backend
knows the calling convention and register pressure, so it can make
better stack-vs-heap decisions than MIR.

*Estimated impact:* 5-15% on closure-heavy code with short-lived lambdas.

### Memory Layout Optimisation

A Kea-native backend controls struct layout. Cranelift takes what it's
given. This unlocks:

- **Discriminant packing.** `Result(T, E)` needs 1 bit for Ok/Err.
  Pack it into a padding byte or pointer tag. Pattern matching becomes
  a bit test, not a memory load.
- **Field reordering for cache locality.** Put hot fields (discriminants,
  frequently accessed data) at offset 0. Cold fields at the end.
  (Opt-in only — declaration order is the default per
  performance-backend-strategy.md §4.)
- **Unboxing across function boundaries.** If the backend knows both
  caller and callee (Kea-to-Kea calls), it can pass `Result(Int, String)`
  as two registers (tag + payload) instead of a heap-allocated box.
  Impossible when using the C ABI.
- **Tag-in-pointer for single-field variants.** `Some(x)` can encode
  the `Some` tag in the pointer's low bits (since allocations are
  aligned). Pattern matching becomes a mask, not a memory load.

### Whole-Program Optimisation

Per-function analysis gives ~70% of the wins. Whole-program analysis
gives 90%+. Lobster achieves 95% RC elision via whole-program ownership
analysis. A Kea-native backend doing whole-module (or LTO-style
cross-module) analysis can:

- **Whole-program devirtualisation.** If `map` is only ever called with
  4 specific closures across the entire program, generate 4 specialised
  versions and dispatch on closure identity. Not just "is this closure
  statically known here" but "across the entire call graph."
- **Whole-program RC elision.** Trace ownership flow across function
  boundaries. If a value is created in A, passed to B, used in B, and
  never stored — the entire retain/release chain across A→B is
  eliminated. No borrow annotation needed; the analysis proves it.
- **Dead effect elimination.** If no handler for `Log` is ever installed
  in the program, all `Log` effect operations are provably dead.
  Eliminate them entirely — including the evidence vector slots.
- **Cross-module effect-guided inlining.** If inlining across a module
  boundary would eliminate an effect dispatch, do it.

### Compound Impact

These optimisations are multiplicative, not additive. A typical compiler
pass does all of: RC operations on IR nodes, closure-based traversals,
effect handler dispatch, pattern matching, and allocation. Compound
improvement on a real compiler pass: estimated 2-4x over Cranelift
baseline for the hot paths.

### Numeric Performance: Three Tiers

The naive take — "Kea loses on numeric, just use LLVM" — misses
something. Kea's type system provides information that LLVM *wants*
for vectorisation but usually can't get: non-aliasing proofs.

LLVM's auto-vectoriser is constantly held back by aliasing. C needs
`restrict` (a promise the programmer can break). Rust's borrow checker
provides `noalias` for references but still struggles with
auto-vectorisation in practice. Fortran is fast partly because its
calling convention assumes no aliasing.

Kea gets this for free. `Unique (Array Float64)` is a type-level proof:
no other reference exists, the array can be mutated in place, no
concurrent reads or writes. The vectoriser can go wild. Even without
`Unique`, pure functions (`->`) can't observe aliasing — the compiler
can assume non-aliasing for optimisation purposes.

**Tier 1: Kea-Native Numeric (good enough for most)**

Pure functions over `@unboxed` types with `Unique` arrays:

```kea
@unboxed
struct Vec4
  x: Float32
  y: Float32
  z: Float32
  w: Float32
```

A Kea-native backend keeps `Vec4` in a single XMM/NEON register. Vec4
addition becomes `addps`. `@unboxed` composes with everything else —
put it in a `Unique (Array Vec4)`, map with a pure closure, and the
compiler can vectorise because: unboxed layout + unique ownership +
pure function = no aliasing, no side effects, go fast.

Covers 80% of numeric code: vector math, transformations, accumulations.
Estimated quality: 70-85% of LLVM -O2.

**Tier 2: SIMD Effect (explicit, portable)**

```kea
effect SIMD
  fn load_packed(_ ptr: Ptr Float32, _ count: Int) -> Vec4
  fn store_packed(_ ptr: Ptr Float32, _ val: Vec4) -> Unit
  fn fma(_ a: Vec4, _ b: Vec4, _ c: Vec4) -> Vec4

fn dot_product(a: Unique (Array Float32), b: Unique (Array Float32))
    -> Float32 -[SIMD]>
  let mut acc = SIMD.zero()
  for chunk in a.chunks(4).zip(b.chunks(4))
    let va = SIMD.load_packed(chunk.0)
    let vb = SIMD.load_packed(chunk.1)
    acc = SIMD.fma(va, vb, acc)
  SIMD.horizontal_sum(acc)
```

The handler determines the instruction set:

```kea
handle matrix_multiply(a, b) with
  SIMD -> Avx2Handler    -- x86: AVX2
handle matrix_multiply(a, b) with
  SIMD -> NeonHandler    -- ARM: NEON
handle matrix_multiply(a, b) with
  SIMD -> ScalarHandler  -- fallback: scalar emulation
```

Same kernel code, different hardware backends, swappable at the handler
level. Tail-resumptive handlers compile to direct calls — zero overhead.

**Effects as compilation mode selectors.** This is a compiler
architecture insight, not just an optimisation. When the backend sees
`-[SIMD]>` in a function's effect row, it doesn't just "thread an
evidence vector." It triggers an entirely different codegen strategy:
different register allocator (SIMD-aware, preferring XMM/NEON
registers), different instruction selection rules (prefer packed ops),
different optimisation passes (enable vectorisation, disable RC
coalescing on unboxed values). The effect row is a first-class input
to the backend's compilation strategy selector. Pure code (`->`) gets
one strategy. Effectful code (`-[IO]>`) gets another. SIMD code
(`-[SIMD]>`) gets a third. No other language provides this information
to its backend.

Similar to Rust's `std::simd` or C intrinsics, but with effect-tracked
portability — no `#[cfg]` or `#ifdef`.

**Design tension: effect vs trait.** Leaf SIMD operations like `fma`
don't suspend or interact with control flow — they're instructions, not
effects in the algebraic sense. A trait-based approach (`trait SIMD`
with `impl SIMD for Avx2`) gives the same compile-time portability. The
effect encoding earns its keep when operations genuinely interact with
control flow (e.g., `parallel_reduce` where the handler chooses tree
reduction vs sequential vs GPU dispatch) and when SIMD needs to compose
with other effects in the same function. The final design may use traits
for leaf ops and effects for higher-level dispatch strategies. Either
way, the "effect row as codegen mode selector" insight holds — traits in
the type signature serve the same signalling role to the backend.

Estimated quality: 90-95% of LLVM -O2 for explicit SIMD.

**Tier 3: embed + Foreign Backend (peak)**

For the 1% that needs absolute peak:

```kea
fn matmul(a: Matrix Float32, b: Matrix Float32) -> Matrix Float32
  embed BLAS {
    SGEMM('N', 'N', ${a.rows}, ${b.cols}, ${a.cols},
           1.0, ${a.data}, ${a.rows},
           ${b.data}, ${b.rows},
           0.0, ${result.data}, ${a.rows})
  }
```

Or the `@gpu` recipe from COMPILER-AS-DATA for GPU compute. Don't
compete with LLVM's vectoriser or cuBLAS — call them. The Grammar/embed
system makes this type-safe at the Kea boundary.

**The honest framing:** Kea-native beats LLVM on *functional* patterns
(closures, RC, effects, pattern matching, allocation). For numeric
patterns, Tier 1 is good enough for most code, Tier 2 gives explicit
control with portability, Tier 3 gives peak performance through
interop. The effect system connects all three tiers — no mode switch,
no separate FFI layer. And `Unique T` as a vectorisation enabler is
something C and Rust struggle to match.

### Phased Backend Strategy

```
Phase 0-1: Cranelift only
  - Fast iteration, focus on language semantics
  - MIR contract designed for backend neutrality (see performance-backend-strategy.md)
  - Benchmark baselines established

Phase 2: Debug + Release split
  Debug backend (Kea-native):
    - Minimal optimisation, maximum compile speed
    - Copy-and-patch possible (100x faster than LLVM, ~78% code quality)
    - This is the `kea run` / inner-loop backend
  Release backend (Kea-native, full pipeline):
    - RC fusion, closure devirt, effect compilation, PGO
    - Slower to compile, generates best code
    - This is the `kea build --release` backend

Phase 3: Kea-native primary, Cranelift fallback
  - Self-hosted compiler compiles itself with Kea-native backend
  - Cranelift retained for cross-compilation and new platform bringup
  - Optional LLVM backend for numeric-heavy release builds
```

The key insight: a backend written in Kea for Kea has access to
everything the effect system and type system know. RC semantics, closure
structure, handler dispatch class, allocation lifetime, uniqueness —
all first-class information in the backend's IR, not opaque function
calls. This is the same advantage that V8 has over a generic compiler
for JavaScript, but with static types providing the information instead
of runtime profiling.

## Static PGO: The Type System Already Knows

Traditional PGO is a three-step process: compile with instrumentation,
run on representative workloads, recompile with profile data. The profile
tells the compiler branch frequencies, call targets, allocation patterns,
and loop trip counts. The problem: it requires a representative workload.
If your training run misses production hot paths, PGO makes things worse.

Kea's type system provides much of what PGO discovers empirically:

| What PGO discovers at runtime | What Kea knows at compile time |
|---|---|
| "This branch is taken 99% of the time" | COW uniqueness check: RC==1 is the hot path (reuse analysis proves it) |
| "This indirect call always targets f" | Closure devirtualisation: the callee is statically known |
| "This function is pure (no side effects)" | The effect signature says `->` (pure) |
| "This value is never shared across threads" | No `Send`/`Spawn` in the effect row |
| "This allocation is always 64 bytes" | The type is known, the layout is known |
| "This handler always resumes immediately" | Tail-resumptive handler: static property |
| "This value is never aliased" | `Unique T` — proven by the type system |

A huge chunk of PGO's value is already captured statically. No
instrumentation run, no training workload, no "hope your profile
matches production."

### Where Runtime Profiling Still Wins

The type system genuinely can't know:

- **Pattern match branch weights.** Which of 15 variants appears 90%
  of the time? Only runtime data tells you.
- **Hot function identification.** Which functions account for 80% of
  execution time? Inlining decisions need this.
- **Loop trip counts.** 3 iterations or 3 million? Unrolling depends
  on this.
- **Cache behavior.** Which access patterns cause L1 misses?
- **Allocation site frequency.** Which sites are hit most often?

### Profiling as an Effect

In Kea, profiling is an effect, not binary instrumentation:

```kea
effect Profile
  fn branch_taken(_ site: SiteId, _ branch: Int) -> Unit
  fn call_entered(_ site: SiteId) -> Unit
  fn alloc_hit(_ site: SiteId, _ size: Int) -> Unit

-- Development: collect profiles
handle compile(src) with
  Profile -> FileCollector.new("compile.profile")

-- Production: no profiling (handler eliminated)
handle compile(src) with
  Profile -> Noop   -- zero-cost, tail-resumptive → inlined away
```

Because profiling is an effect:

- **No separate instrumented build.** Want profiling? Add the handler.
  Don't want it? Remove it. Same binary.
- **The effect system proves profiling doesn't affect semantics.**
  `Profile` is write-only — the compiler can verify this.
- **Different handlers for different strategies.** Sampling, counters,
  statistical — all just different handlers for the same effect.
- **Minimal overhead.** A tail-resumptive `Profile` handler compiles
  to a direct call (see §4 above). No evidence vector manipulation.

### The Self-Hosting PGO Loop

The compiler compiling itself is a natural PGO feedback loop:

1. Compile the compiler with `Profile` handler enabled
2. Use the compiler to compile a large Kea project (or itself)
3. Feed the profile back into the compiler's optimisation passes
4. Recompile the compiler with the profile
5. The compiler is now optimised for exactly the workload it performs

This is what GCC does with `make profiledbootstrap`. But Kea's version
is cleaner: the profiling is an effect, the profile data is a Kea value,
and the optimisation passes that consume the profile are Kea functions.
The compiler optimises itself, using itself, for itself.

### Bootstrapping Acceleration

Most compilers self-host for ergonomic reasons. Kea self-hosts for
*performance* reasons — each generation is a better optimiser running
on its own optimisation-amenable code:

- **Gen 1:** Kea compiler compiled by Rust bootstrap. Baseline
  performance. No Kea-specific optimisations.
- **Gen 2:** Kea compiler compiled by Gen 1. Now benefits from reuse
  analysis, borrow inference, effect-guided optimisation on its own IR
  passes. Generates better code than Gen 1 could.
- **Gen 3:** Kea compiler compiled by Gen 2 (which was faster and
  produced better code). If Gen 2 added better inlining heuristics,
  Gen 3's code is better. And Gen 3 compiles faster because Gen 2
  was faster.

This converges (typically 2-3 generations), but each generation sees
real gains. GCC's `make profiledbootstrap` does a 3-stage bootstrap
and typically gains 5-10% per stage. Kea's version is more interesting
because the improvements aren't just PGO — they include semantic
optimisations that earlier compiler versions couldn't perform.

### Beyond PGO: Specialisation-Guided Optimisation

PGO is reactive. Kea can be proactive because of the type system:

**Effect-row monomorphisation.** When a polymorphic function is called
at a known effect row, generate a specialised version:

```kea
fn map(xs: List a, f: a -> b -[e]>) -> List b -[e]>

-- Called with e = Pure: specialise to no evidence threading,
--   inline closure, TRMC the recursion, reuse list nodes
-- Called with e = [IO, Fail String]: different specialised version
--   that handles the evidence vector
```

Same source code, different generated code, driven by the effect row.

**Effect-guided inlining.** Traditional inlining uses code size and
call frequency. Kea adds a third signal: effect elimination. If inlining
a function would collapse an effect dispatch (because the handler is
visible at the call site), that inlining is disproportionately valuable:

```kea
fn log_info(msg: String) -[Log]>
  Log.write(Level.Info, msg)

handle
  log_info("starting")  -- inline → Log.write becomes direct call to handler
with
  Log -> ConsoleLogger
```

Prioritise inlining decisions that eliminate effects — information
LLVM/Cranelift fundamentally cannot have.

**Speculative devirtualisation.** For closures that aren't statically
known but are *usually* one specific function (discovered via profiling):

```asm
; Is this the common closure?
cmp [closure_ptr + fn_offset], expected_fn
jne slow_path
; Fast path: inline the expected function body
...
slow_path:
call [closure_ptr + fn_offset]   ; generic indirect call
```

V8 does this for JavaScript. With PGO data, an AOT compiler can too.

### The Full Optimisation Stack

| Layer | What it provides | Information source |
|---|---|---|
| Type system | Uniqueness, purity, effect rows, layouts | Static (compile time) |
| Unique-as-noalias | Vectorisation enabler for array code (what C needs `restrict` for) | Static (type system) |
| Reuse analysis | RC==1 proofs, reuse tokens | Static (MIR pass) |
| TRMC + native backend | List/tree traversals as tight write-cursor loops | Static (MIR pass + backend) |
| Auto borrow inference | Eliminate most RC ops | Static (MIR pass) |
| Effect-guided optimisation | Handler inlining, evidence elimination, parallelism | Static (effect signatures) |
| Effect-as-codegen-mode | SIMD/Pure/IO trigger different backend strategies | Static (effect row) |
| Kea-native backend | RC fusion, closure devirt, escape analysis, custom calling convention | Static (semantic knowledge) |
| Whole-program analysis | Cross-module RC elision, dead effect elimination, global devirt | Static (link-time) |
| PGO via Profile effect | Branch weights, call frequencies, hot functions | Runtime (profile data) |
| Effect-row specialisation | Monomorphise on type + effect row | Static + profile guided |
| Allocation specialisation | Size-class fast paths, free-list routing | Runtime (profile data) |

The top nine layers are what you get from the type system and semantic
knowledge. The bottom three are what PGO adds. Together, they form an
optimisation stack no general-purpose compiler can replicate, because
the information that drives the optimisations is encoded in the
language's semantics.

### The Honest Assessment

Can this beat LLVM -O2 on all code? No. LLVM has decades of loop
optimisation, vectorisation, and alias analysis for C-style code.

Can this beat LLVM -O2 on Kea-idiomatic code? The architectural ceiling
says yes. Every optimisation above exploits information invisible to
LLVM. Whether the ceiling is reached is an empirical question — but
the structural advantage is real: **the language knows things about its
own code that general-purpose backends can't know.**

## Acceptance Gates

Concrete, measurable criteria that turn the vision into falsifiable
hypotheses. These gate investment decisions — if a gate isn't met,
investigate before continuing.

### Phase 1: Self-Hosting Baseline

- [ ] Compiler compiles itself via Cranelift (correctness)
- [ ] Benchmark suite established: rbtree, map/filter, parser,
      typechecker workloads
- [ ] Baseline numbers for all Performance Targets rows
- [ ] Gen 1 vs Gen 2 bootstrap comparison (measure actual vs expected
      improvement from reuse/borrow/TRMC on compiler's own IR passes)
- [ ] Memory management overhead measured (<20% target)
- [ ] Retain/release counts before/after borrow inference quantified

### Phase 2: Kea-Native Backend

- [ ] Debug backend passes full compiler test suite
- [ ] Debug compile speed measured ≥2x Cranelift on self-compilation
- [ ] Release code quality ≥90% of Cranelift on benchmark suite
- [ ] At least 3 of items 1-10 from §What a Kea-Native Backend Enables
      show measurable improvement over Cranelift on real workloads
- [ ] FFI trampoline overhead measured (<5ns target)
- [ ] Closure devirtualisation hit rate measured on compiler workload

### Phase 3: Kea-Native Primary

- [ ] Self-hosted compiler passes full test suite on native backend
- [ ] Benchmark parity or improvement vs Cranelift on all target rows
- [ ] PGO loop (Profile effect) demonstrates measurable gain on
      self-compilation
- [ ] Gen 2 vs Gen 3 bootstrap acceleration converges (diminishing
      returns measured)

If Phase 2 gates aren't met after reasonable investment, fall back to
Cranelift primary + targeted MIR-level optimisations. The language-level
wins (§Unique Pipeline through §Static PGO) deliver value regardless
of backend choice.

## Implementation Notes

This brief is a design document, not an implementation plan. The
techniques described here are delivered by other briefs:

- **Reuse analysis, auto borrow, TRMC, FIP** → 0f Step 3b-3f
- **Unique T** → 0f Steps 1-2
- **Arena/Alloc effect** → 0f Step 7 + future Alloc effect brief
- **Effect-tracked parallelism** → Phase 1-2 (requires self-hosting)
- **Incremental queries** → Phase 2 (requires Salsa-style framework)
- **Cranelift backend** → 0d (done)
- **Kea-native backend** → Phase 2-3 (requires self-hosting + MIR contract)
- **Profile effect + PGO** → Phase 2-3 (requires self-hosting + Profile effect)
- **MIR contract + backend interface** → performance-backend-strategy.md

The purpose of this brief is to ensure these pieces are designed with
the self-hosting compiler in mind. The compiler is the first program
that benefits from all of them together.

## Key References

- **Perceus**: Reinking, Xie, de Moura, Leijen. "Perceus: Garbage Free
  Reference Counting with Reuse." PLDI 2021.
- **FP²**: Lorenzen, Leijen, Swierstra. "FP²: Fully in-Place Functional
  Programming." ICFP 2023.
- **TRMC**: Leijen. "Tail Recursion Modulo Context: An Equational
  Approach." POPL 2023.
- **Lean 4 RC**: Ullrich, de Moura. "Counting Immutable Beans." IFL 2019.
- **Sorbet**: Stripe. "Sorbet: A fast, powerful type checker for Ruby."
  OOPSLA 2019. (Parallel pure-function-per-method architecture.)
- **Salsa**: rust-analyzer team. Demand-driven incremental computation
  framework. (Query effect pattern.)
- **Copy-and-patch**: Xu, Kjolstad. "Copy-and-Patch Compilation."
  OOPSLA 2021. (CPython 3.13+ JIT technique. 100x faster than LLVM -O0
  compilation, ~78% of LLVM -O2 runtime quality.)
- **Go SSA backend**: Cox et al. Go 1.7+ SSA backend. ~15K LOC for
  first architecture, ~1.5 FTE-years. Custom calling convention.
- **OCaml native**: OCaml native-code compiler. ~15-25K LOC. Inline
  allocation (4 instructions), custom calling convention, tag-in-pointer.
