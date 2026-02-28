# Brief: Phase 1b/1c — Compiler in Kea + Bootstrap

**Status:** ready
**Priority:** v1-critical
**Depends on:** phase-1a-ffi (Cranelift bindings), all Phase 0 complete
**Blocks:** Phase 2 (native backend, ecosystem)
**Also read:**
- [COMPILER-AS-DATA](../../docs/COMPILER-AS-DATA.md) — the architectural thesis
- [Self-hosting perf](../design/self-hosting-perf.md) — performance strategy
- [Phase 1a FFI](phase-1a-ffi.md) — Cranelift bindings this depends on

## Motivation

Self-hosting is the ultimate design validation. The compiler exercises
every language feature in a real, complex program: pattern matching
on IR, effects for diagnostics, Unique for zero-copy transformations,
handlers for pluggable compilation strategies, row polymorphism for
extensible passes.

The strategy is **pass-by-pass validation**: write each compiler pass
in Kea, test it against the Rust bootstrap's output. No big-bang
rewrite. Each pass is independently verifiable. Once all passes are
ported and verified, a three-stage bootstrap proves correctness and
drops the Rust dependency.

## Strategy: Pass-by-Pass Validation

Each pass is written in Kea, compiled by the Rust bootstrap, and
tested by comparing its output to the Rust implementation's output
on the full test corpus.

```
Rust lexer → Rust parser → Rust typechecker → Rust MIR → Rust codegen
  ↕ test      ↕ test         ↕ test             ↕ test     ↕ test
Kea lexer  → Kea parser  → Kea typechecker  → Kea MIR  → Kea codegen
```

"Identical" means structurally equivalent — not bit-identical, but
semantically equivalent modulo representation details. The comparison
framework serialises IR to a canonical form and diffs.

### Validation Protocol

For each pass:

1. Write the Kea implementation
2. Compile it with the Rust bootstrap
3. Run both Kea and Rust implementations on the full test corpus
4. Compare outputs (structural equality)
5. If outputs differ, investigate — could be a Kea bug or a Rust bug
6. Once equivalent, the Kea pass replaces the Rust pass in the pipeline

The test corpus is the existing integration test suite plus the
compiler's own source code (self-application test).

## Pass Order

Write passes in dependency order. Each pass is a commit boundary.

### 1. Lexer

Tokenise Kea source into a token stream.

- **Input:** `String` (source code)
- **Output:** `List Token`
- **Validation:** token-by-token comparison with Rust lexer
- **Kea features used:** pure functions, pattern matching, enums
- **Complexity:** low — mostly character classification and state machine

```kea
fn tokenise(source: String) -> List Token
  -- pure function, no effects needed
```

### 2. Parser

Recursive descent + Pratt for expressions. Indentation handling.

- **Input:** `List Token`
- **Output:** `Ast` (or `Fail ParseError`)
- **Validation:** AST structural comparison with Rust parser
- **Kea features used:** Fail, recursion, enums, structs
- **Complexity:** medium — indentation tracking adds state

```kea
fn parse(tokens: List Token) -[Fail ParseError]> Ast
```

### 3. Name Resolution + HIR Lowering

Resolve names, desugar syntax (with-blocks, string interpolation,
`?` operator), build scope tree.

- **Input:** `Ast`
- **Output:** `Hir`
- **Validation:** HIR comparison with Rust lowering pass
- **Kea features used:** State (symbol table), handlers, Map, Set
- **Complexity:** medium — scope rules and desugaring

```kea
fn lower(ast: Ast) -[State SymbolTable, Fail ResolutionError, Diagnose]> Hir
```

### 4. Type Inference

HM inference with Rémy-style row unification, effect inference,
trait resolution, UMS dispatch.

- **Input:** `Hir`
- **Output:** `TypedHir` (annotated with inferred types and effects)
- **Validation:** inferred types match Rust typechecker on test corpus
- **Kea features used:** State (substitution, unification state),
  Fail (type errors), complex data structures (Type, Row, Constraint)
- **Complexity:** **high** — this is the hardest pass. Budget extra time.

```kea
fn infer(hir: Hir) -[State InferState, Fail TypeError, Diagnose]> TypedHir
```

The type inference engine is ~1.5MB of Rust. Translating it to
idiomatic Kea means replacing `&mut InferCtx` parameter threading
with State effect, `Result<T, TypeError>` with `Fail TypeError`,
and mutable `HashMap` lookups with effect-based operations. The
algorithm stays the same; the expression changes.

### 5. MIR Lowering

Lower typed HIR to mid-level IR. Pattern match compilation
(decision trees), closure conversion, RC insertion.

- **Input:** `TypedHir`
- **Output:** `Mir`
- **Validation:** MIR structural comparison
- **Kea features used:** Unique T for IR ownership, pattern matching
- **Complexity:** medium-high — pattern match compilation is intricate

```kea
fn lower_to_mir(typed: TypedHir) -[Fail LowerError]> Mir
```

### 6. Optimisation Passes

Each is a pure MIR→MIR function. Constant folding, dead code
elimination, inlining, borrow inference, reuse analysis.

- **Input:** `Mir`
- **Output:** `Mir`
- **Validation:** optimised MIR comparison per pass
- **Kea features used:** Unique for in-place transformation, pure signatures
- **Complexity:** varies per pass, but each is independently testable

```kea
fn constant_fold(mir: Unique Mir) -> Unique Mir    -- pure!
fn eliminate_dead_code(mir: Unique Mir) -> Unique Mir
fn infer_borrows(mir: Unique Mir) -> Unique Mir
```

These passes are pure (`->`). The effect system proves it. This is
the first real use of the "pure passes parallelise" architecture
from COMPILER-AS-DATA.

### 7. Codegen Wrapper

Orchestrate Cranelift via the FFI bindings from Phase 1a.

- **Input:** `Mir`
- **Output:** `Bytes` (machine code)
- **Validation:** generated binaries produce identical output
- **Kea features used:** FFI, Codegen effect, Ptr operations
- **Complexity:** medium — mostly translating MIR to Cranelift IR

```kea
fn codegen(mir: Mir) -[IO, Fail CodegenError]> Bytes
  Cranelift.with_module |module|
    for func in mir.functions
      Cranelift.define_function(module, func.name, ...)
    Cranelift.emit(module)
```

### 8. Driver

Tie all passes together. CLI argument parsing, file IO, module
resolution, the full compilation pipeline.

- **Input:** command-line arguments, source files
- **Output:** compiled binary or error messages
- **Kea features used:** IO, module system, handler composition

```kea
fn main() -[IO]> Unit
  let args = parse_cli_args()
  case args.command
    Build { input, output } ->
      with Diagnostics.to_stderr
        let binary = compile_file(input)
        write_file(output, binary)
    Run { input } ->
      with Diagnostics.to_stderr
        let binary = compile_file(input)
        jit_execute(binary)
    -- ...
```

## The Compiler Uses Kea's Features

The self-hosted compiler is the showcase for Kea's design:

- **Effect-tracked passes.** The effect signature is the capability
  contract. A pure optimisation pass provably can't emit diagnostics.
- **Handlers for diagnostics.** `with Diagnose -> collect_errors()`
  for testing, `with Diagnose -> pretty_print_stderr()` for CLI,
  `with Diagnose -> structured_json()` for LSP.
- **Unique IR pipeline.** Zero RC through the hot path. Each pass
  owns its IR exclusively.
- **Pattern matching everywhere.** Exhaustiveness checking catches
  missing cases when new IR nodes are added.
- **Row polymorphism for partial passes.** An optimisation that
  handles `Let`, `If`, `Call` and passes everything else through.

## Three-Stage Bootstrap (1c)

Once all passes are ported and validated:

```
Stage 1: Rust bootstrap compiles Kea compiler source → Binary A
Stage 2: Binary A compiles Kea compiler source       → Binary B
Stage 3: Binary B compiles Kea compiler source       → Binary C

Requirement: B and C produce identical output on the test suite.
```

B and C may not be bit-identical (different compilers may make
different codegen choices). The requirement is **semantic
equivalence**: B and C produce identical output on every input.

### Verification

1. Run the full test suite through Binary B and Binary C
2. Compare all outputs — they must be identical
3. Additionally: compile a corpus of programs with B and C, compare
   generated binaries functionally (run each, compare stdout/stderr)

### Dropping Rust

Once the three-stage bootstrap passes:

1. The Kea compiler is the source of truth
2. The Rust bootstrap is archived (kept for historical reference)
3. CI builds use Binary B to compile Binary C, verifies equivalence
4. New releases are built by self-compilation

### What Ships

```
kea build hello.kea    → native binary
kea run hello.kea      → JIT execute
kea test               → run test suite
kea fmt                → format code
```

Self-contained native binary. Cranelift via FFI for codegen. No
Rust toolchain required to use Kea.

## Definition of Done

### 1b: Compiler in Kea
- [ ] Every compiler pass exists in Kea
- [ ] Pass-by-pass output matches Rust bootstrap on full test corpus
- [ ] Kea compiler can compile itself (self-application)
- [ ] All existing tests pass when compiled by the Kea compiler
- [ ] Effect signatures on passes are accurate (not over-declared)
- [ ] Idiomatic Kea — effects for state/errors, not parameter threading

### 1c: Three-Stage Bootstrap
- [ ] Stage 2 and Stage 3 produce semantically equivalent output
- [ ] CI verifies bootstrap equivalence on every commit
- [ ] Kea binary ships without Rust toolchain dependency
- [ ] `kea build`, `kea run`, `kea test`, `kea fmt` work from self-hosted binary

## Risks

**Type inference port complexity.** The type inference engine is the
most complex pass (~1.5MB Rust). Row unification, effect inference,
constraint solving, trait resolution — all deeply intertwined.
Mitigation: port it last among the core passes, after the simpler
passes have validated the translation patterns.

**Bootstrap divergence.** Subtle differences between Kea and Rust
implementations on edge cases are hard to debug. Mitigation:
pass-by-pass testing catches divergence early, before it compounds.

**Performance regression.** The Kea compiler may be slower than the
Rust bootstrap initially. Expected and acceptable — Phase 1d
addresses performance. Correctness first.

**IR serialisation for comparison.** Comparing IR across Rust/Kea
boundary requires a common serialisation format. Design this
format early (probably JSON of a canonical IR representation).

## Process

1. Build the IR comparison framework first (serialize Rust IR and
   Kea IR to the same format, diff them)
2. Port passes in order: lexer → parser → name resolution →
   type inference → MIR lowering → optimisation → codegen → driver
3. Commit per pass. CI runs comparison tests after each.
4. After all passes: three-stage bootstrap
5. Debug any bootstrap discrepancies
6. Set up CI for ongoing bootstrap verification
7. Archive Rust bootstrap
