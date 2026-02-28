# Brief: Self-Hosting Compiler Performance Strategy

**Status:** design
**Priority:** v1
**Depends on:** 0f (memory model), 0g (advanced types), Phase 1 (self-hosting)
**Blocks:** nothing (design doc, informs implementation)
**Also read:**
- [COMPILER-AS-DATA](../../docs/COMPILER-AS-DATA.md) — the architectural thesis
- [0f-memory-model](../in-progress/0f-memory-model.md) — Step 3 memory optimisation pipeline
- [performance-backend-strategy](performance-backend-strategy.md) — MIR/backend design

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

The entire compilation pipeline has **zero RC overhead**. No increments,
no decrements, no COW checks, no atomic operations. Every transformation
is guaranteed in-place. This isn't an optimisation — it's a type-level
proof that the compiler never does unnecessary work.

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
| Parallel compilation | Sorbet (per-method), Go (per-pkg) | Par per function with type-level safety proof (effects + Unique) |
| Arena allocation | Every C compiler | Alloc effect makes it composable and safe |
| Incremental queries | rust-analyzer | Query effect tracks dependencies in the type system |
| Zero-RC IR pipeline | Nobody | Unique T through linear pipeline eliminates RC entirely |

## Performance Targets

| Dimension | Target | Basis |
|-----------|--------|-------|
| IR pass throughput | Zero-allocation (reuse + Unique) | Perceus benchmarks, Lean validation |
| Memory management overhead | <20% of runtime | Lean's 17% vs OCaml's 90% |
| Codegen speed | Cranelift: 20-40% faster than LLVM | Cranelift 2024 benchmarks |
| Type checking throughput | 100K+ lines/sec/core | Sorbet architecture |
| Parallel scaling | 2-4x on 4+ cores | Sorbet, rustc codegen |
| Incremental rebuilds | Sub-100ms for single-file edits | Salsa-style early cutoff |

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

The realistic ambition: **one of the fastest functional language
compilers ever built**, matching or exceeding OCaml's compilation speed
but with a richer type system (effects, row polymorphism, Unique). Not
because of any single breakthrough, but because the language's own
features — effects, uniqueness, immutability — are exactly what a
compiler optimiser wants to reason about.

## Implementation Notes

This brief is a design document, not an implementation plan. The
techniques described here are delivered by other briefs:

- **Reuse analysis, auto borrow, TRMC, FIP** → 0f Step 3b-3f
- **Unique T** → 0f Steps 1-2
- **Arena/Alloc effect** → 0f Step 7 + future Alloc effect brief
- **Effect-tracked parallelism** → Phase 1-2 (requires self-hosting)
- **Incremental queries** → Phase 2 (requires Salsa-style framework)
- **Cranelift backend** → 0d (done)

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
