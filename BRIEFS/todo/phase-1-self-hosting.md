# Brief: Phase 1 — Self-Hosting Compiler

**Status:** ready
**Priority:** v1-critical
**Depends on:** 0d1, 0e, 0f, 0g (all Phase 0 complete)
**Blocks:** Phase 2 (native backend, ecosystem)
**Also read:**
- [COMPILER-AS-DATA](../../docs/COMPILER-AS-DATA.md) — the architectural thesis
- [Self-hosting perf](../design/self-hosting-perf.md) — performance strategy
- [Packaging, FFI, comptime](../design/packaging-ffi-comptime.md) — FFI design
- [Performance backend strategy](../design/performance-backend-strategy.md) — MIR/backend contract

## Motivation

Self-hosting is the ultimate design validation. Every language feature
gets exercised in a real, complex program. Issues found here are issues
every serious user would hit.

The strategy: **pass-by-pass validation**. Write each compiler pass in
Kea, test it against the Rust bootstrap's output. No big-bang rewrite.
Each pass is independently verifiable. Cranelift stays as the backend
via FFI — writing a native backend is Phase 2-3 work.

By Phase 1's start, all Phase 0 features are available: full type
system (GADTs, associated types, supertraits), effects and handlers,
memory model (Unique, borrow, Perceus), @derive, and a battle-tested
stdlib. The stdlib has been exercising the compiler for months — Tier 0
through Tier 3 have already validated every major compilation phase.

## Phase 1a: FFI and Cranelift Bindings

**Goal:** Kea can call C libraries, specifically Cranelift's C API.

### C FFI

Implement `extern "C"` function declarations and `unsafe` blocks per
the packaging-ffi-comptime brief:

```kea
extern "C" fn cranelift_module_new() -> Ptr CraneliftModule
extern "C" fn cranelift_func_create(
  module: Ptr CraneliftModule,
  name: Ptr U8,
  sig: Ptr CraneliftSig,
) -> Ptr CraneliftFunc
```

Key deliverables:
- `extern "C"` declarations in Kea source
- `unsafe` blocks for raw pointer operations
- Static linking of C libraries into Kea binaries
- Ptr operations: `Ptr.null`, `Ptr.offset`, `Ptr.read`, `Ptr.write`
- C string interop: `String.as_c_str`, `String.from_c_str`
- Opaque handle pattern: wrap C pointers in safe Kea types

### Cranelift Bindings

Write `cranelift.kea` — a safe Kea wrapper around Cranelift's C API.
This is the first real FFI library and validates the FFI design.

```kea
struct Cranelift

  effect Codegen
    fn define_func(name: String, sig: FuncSig, body: FuncBody) -> FuncId
    fn emit_module() -> Bytes

  fn with_module(f: () -[Codegen]> A) -[IO, Fail CraneliftError]> A
    -- creates Cranelift module, handles Codegen effect,
    -- translates operations into C API calls
```

The Cranelift binding wraps codegen as a Kea effect. This is the
same pattern COMPILER-AS-DATA describes — compilation stages are
effects, handlers provide the implementation. Phase 1a proves
the architecture works before the full compiler is ported.

### Validation

- Kea program using FFI can call a C function and get the right result
- Cranelift bindings can JIT-compile a simple function and execute it
- AOT binary with linked C library works end-to-end
- Memory safety: no leaks, no use-after-free (valgrind/ASAN clean)

## Phase 1b: Compiler in Kea, Pass by Pass

**Goal:** Rewrite every compiler pass in Kea, tested against the Rust
bootstrap at each step.

### Strategy: Pass-by-Pass Validation

Each pass is written in Kea, compiled by the Rust bootstrap, and
tested by comparing its output to the Rust implementation's output
on a comprehensive test corpus. This gives confidence at every step
without requiring a big-bang switch.

```
Rust lexer → Rust parser → Rust typechecker → Rust MIR → Rust codegen
  ↕ test      ↕ test         ↕ test             ↕ test     ↕ test
Kea lexer  → Kea parser  → Kea typechecker  → Kea MIR  → Kea codegen
```

At each step, the Kea pass and Rust pass must produce identical
output on the full test suite. "Identical" means structurally
equivalent IR — not necessarily bit-identical, but semantically
identical modulo representation details.

### Pass Order

Write passes in dependency order. Each pass is a commit boundary.

**1. Lexer** — tokenize Kea source into a token stream.
- Input: String (source code)
- Output: List Token
- Validation: token-by-token comparison with Rust lexer
- Exercises: String operations, pattern matching, List construction
- Kea features used: pure functions, pattern matching, enums

**2. Parser** — recursive descent + Pratt for expressions.
- Input: List Token
- Output: Ast (or Fail ParseError)
- Validation: AST structural comparison with Rust parser
- Exercises: Fail effect, recursive data structures, complex matching
- Kea features used: Fail, recursion, enums, structs

**3. Name resolution + HIR lowering** — resolve names, desugar.
- Input: Ast
- Output: Hir
- Validation: HIR comparison with Rust lowering pass
- Exercises: State effect (symbol table), Map lookups
- Kea features used: State, handlers, Map, Set

**4. Type inference** — HM inference with row unification.
- Input: Hir
- Output: TypedHir (annotated with types)
- Validation: inferred types match Rust typechecker on test corpus
- Exercises: the entire type system, effect inference, constraint solving
- Kea features used: State (substitution), Fail (type errors), complex data structures
- This is the hardest pass. Expect iteration.

**5. MIR lowering** — lower typed HIR to mid-level IR.
- Input: TypedHir
- Output: Mir
- Validation: MIR structural comparison
- Exercises: IR transformations, pattern match compilation

**6. Optimisation passes** — each is a pure MIR→MIR function.
- Input: Mir
- Output: Mir
- Validation: optimised MIR comparison per pass
- These are pure (`->`) — the compiler can verify this
- Exercises: Unique T for in-place IR transformation, reuse analysis

**7. Codegen wrapper** — orchestrate Cranelift via the FFI bindings.
- Input: Mir
- Output: Bytes (via Codegen effect from 1a)
- Validation: generated binaries produce identical output
- Exercises: FFI, effect-based codegen, Ptr operations

**8. Driver** — tie all passes together, handle CLI args.
- Input: command-line arguments, source files
- Output: compiled binary or error messages
- Exercises: IO, module system, the full pipeline
- This is the `fn main() -[IO]> Unit` entry point

### The Compiler Uses Kea's Features

The self-hosted compiler is the showcase for Kea's design. It should
use every feature the language offers:

- **Effect-tracked passes.** `fn infer(hir: Hir) -[State InferState, Fail TypeError, Diagnose]> TypedHir`. The effect signature is the capability contract.
- **Handlers for diagnostics.** `handle compile(src) with Diagnose -> collect_errors()`. Different handlers for CLI (pretty-print), LSP (structured), testing (assert).
- **Unique IR pipeline.** `fn optimize(mir: Unique Mir) -> Unique Mir`. Zero RC through the hot path.
- **Pattern matching everywhere.** The compiler is a series of pattern matches over IR. Exhaustiveness checking catches missing cases.
- **Row polymorphism for partial passes.** An optimisation that handles `Let`, `If`, `Call` and passes everything else through via a row variable.

### Validation Protocol

For each pass:

1. Write the Kea implementation
2. Compile it with the Rust bootstrap
3. Run both Kea and Rust implementations on the full test corpus
4. Compare outputs (structural equality, not bit equality)
5. If outputs differ, investigate — could be a Kea bug or a Rust bug
6. Once identical, the Kea pass replaces the Rust pass in the pipeline

The test corpus is the existing integration test suite plus the
compiler's own source code (self-application test).

## Phase 1c: Three-Stage Bootstrap

**Goal:** Prove the self-hosted compiler is correct. Drop Rust.

### The Bootstrap Sequence

```
Stage 1: Rust bootstrap compiles Kea compiler source → Binary A
Stage 2: Binary A compiles Kea compiler source       → Binary B
Stage 3: Binary B compiles Kea compiler source       → Binary C

Requirement: B and C produce identical output on the test suite.
```

B and C may not be bit-identical (different compilers may make
different but equivalent codegen choices). The requirement is
**semantic equivalence**: B and C produce identical output on every
input in the test corpus.

### Dropping Rust

Once the three-stage bootstrap passes:

1. The Kea compiler is the source of truth
2. The Rust bootstrap is archived (kept for historical reference)
3. CI builds use Binary B to compile Binary C and verifies equivalence
4. New releases are built by self-compilation

### What Ships

The self-hosted Kea compiler ships as a native binary. It uses
Cranelift via FFI for code generation. Users install `kea` and it
works — no Rust toolchain required.

```
kea build hello.kea    → native binary
kea run hello.kea      → JIT execute
kea test               → run test suite
kea fmt                → format code
```

## Phase 1d: Compiler Improvements in Kea

**Goal:** Now that the compiler is in Kea, use the language's own
features to make it better.

### Incremental Compilation via Query Effect

Salsa-style demand-driven incremental computation:

```kea
effect Query
  fn input(key: FileId) -> Source
  fn memo(key: QueryKey) -> QueryResult

fn typecheck(file: FileId) -[Query, Diagnose]> Types
  let src = Query.input(file)
  let ast = Query.memo(ParseQuery(file))
  let types = Query.memo(InferQuery(ast))
  types
```

Content-addressed hashing on immutable IR nodes gives early cutoff:
if a whitespace-only edit doesn't change the AST hash, all downstream
passes are skipped. The `Query` effect tracks dependencies
automatically — no manual Salsa annotations.

Target: sub-100ms incremental rebuilds for single-file edits.

### Parallel Compilation

Pure passes parallelise automatically:

```kea
let optimized = Par.map(module.functions, optimize)
-- Effect system proves optimize is pure → safe to parallelise
-- Unique types prove the data doesn't alias → zero-cost handoff
```

Target: 2-4x scaling on 4+ cores for optimisation and codegen.

### Arena-Scoped Phases

```kea
fn compile_file(src: String) -> Bytes
  with Arena.scoped(4096)
    let ast = parse(src)
    let hir = lower(ast)
    -- arena freed here, all AST/HIR nodes gone at once
  let mir = optimize(lower_to_mir(hir))
  codegen(mir)
```

Bump allocation for parse/lower phases. Bulk deallocation at scope
exit. Target: 2-5x allocation throughput from cache locality.

### Error Message Investment

With the compiler in Kea, error messages become first-class:

- Row-diff errors: show what fields/effects are missing vs present
- Effect provenance: trace where an effect requirement came from
- Stable error codes: E0001-style, documented, searchable
- Snapshot tests for every error message (regression-proof quality)

This is 0h work that naturally lands here because the compiler is
now in Kea and can use effects for diagnostic collection.

## Definition of Done

### 1a: FFI and Cranelift Bindings
- [ ] `extern "C"` declarations compile and link
- [ ] `unsafe` blocks work for Ptr operations
- [ ] Cranelift bindings can JIT-compile and execute a function
- [ ] AOT binary with static-linked C library works
- [ ] ASAN/valgrind clean on FFI tests

### 1b: Compiler in Kea
- [ ] Every compiler pass exists in Kea
- [ ] Pass-by-pass output matches Rust bootstrap on full test corpus
- [ ] Kea compiler can compile itself (self-application)
- [ ] All existing tests pass when compiled by the Kea compiler
- [ ] Effect signatures on passes are accurate (not over-declared)

### 1c: Three-Stage Bootstrap
- [ ] Stage 2 and Stage 3 produce semantically equivalent output
- [ ] CI verifies bootstrap equivalence on every commit
- [ ] Kea binary ships without Rust toolchain dependency
- [ ] `kea build`, `kea run`, `kea test`, `kea fmt` work from self-hosted binary

### 1d: Compiler Improvements
- [ ] Incremental compilation: sub-100ms on single-file edits
- [ ] Parallel passes: measurable speedup on 4+ cores
- [ ] Arena allocation: measurable improvement on parse/lower phases
- [ ] Error messages: snapshot-tested, stable error codes

## Process

### Phase 1a (~2 weeks)
1. Implement `extern "C"` in parser, typechecker, and codegen
2. Implement `unsafe` blocks
3. Write Cranelift C API bindings
4. Validate with end-to-end JIT and AOT tests

### Phase 1b (~4-6 weeks)
1. Port passes in order: lexer → parser → name resolution →
   type inference → MIR lowering → optimisation → codegen → driver
2. Commit per pass. CI runs comparison tests after each.
3. Type inference will take the most time — budget accordingly.

### Phase 1c (~1-2 weeks)
1. Run three-stage bootstrap
2. Debug any discrepancies
3. Set up CI for bootstrap verification
4. Archive Rust bootstrap

### Phase 1d (~2-4 weeks, ongoing)
1. Query effect + incremental compilation
2. Par.map on pure passes
3. Arena-scoped allocation
4. Error message quality pass

## Risks

**Type inference port complexity.** The type inference engine is the
most complex pass (row unification, effect inference, constraint
solving). Budget extra time and expect iteration.

**FFI stability.** Cranelift's C API may not be stable. Pin a specific
Cranelift version and wrap unstable APIs behind a compatibility layer.

**Bootstrap divergence.** If the Kea and Rust implementations produce
subtly different results on edge cases, debugging is hard. Mitigated
by pass-by-pass testing rather than big-bang comparison.

**Performance regression.** The Kea compiler may be slower than the
Rust bootstrap initially (before 1d optimisations). This is expected
and acceptable — correctness first, then performance.
