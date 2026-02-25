# Kea Implementation Roadmap v2

## Syntax Decision (Locked)

Indentation-sensitive. Struct-everything. No pipes. UMS for chaining.
No optional braces. No bare top-level functions. No |> operator.

Parser consequence: Rill's parser architecture (recursive descent +
Pratt) transfers as a reference, but block handling needs a full
rewrite for INDENT/DEDENT token emission. Estimated: 1 week
dedicated parser work.

---

## Rill Codebase Inventory (Actual)

Rill is substantially larger than earlier estimates. Current state:

| Crate              | Size    | Kea transfer status |
|--------------------|---------|---------------------|
| rill-infer         | 1.54 MB | **Core reuse** — row unification, HM inference, constraint provenance. Needs: effect rows, handler typing, uniqueness. Tests: massive asset. |
| rill-eval          | 1.07 MB | **Structural reference only** — Kea targets native, not tree-walking. Stdlib patterns (collections, IO, JSON, time, testing) inform Kea stdlib design. Actor runtime patterns transfer conceptually. |
| rill-syntax        | 420 KB  | **Architecture reuse** — recursive descent + Pratt transfers. Block handling rewritten for indentation. Lexer rewritten for Kea keywords/tokens. |
| rill-mcp           | 371 KB  | **Direct adaptation** — compiler-as-MCP-server pattern transfers wholesale. Swap Rill semantics for Kea semantics. Same tool surface (type_check, evaluate, diagnose, get_type). |
| rill-lsp           | 205 KB  | **Direct adaptation** — hover, completions, diagnostics, definition, symbols. Backend changes to Kea type system; LSP protocol layer unchanged. |
| rill-df            | 164 KB  | **Does not transfer** — DataFrame-specific. |
| rill-mir           | 161 KB  | **Partial reference** — MIR design informs Kea's IR. DataFusion lowering doesn't transfer. Optimisation pass structure transfers. |
| rill-fmt           | 154 KB  | **Architecture reuse** — formatter structure transfers. Rules rewritten for indentation-based syntax. |
| rill-codegen       | 82 KB   | **Direct reuse** — Cranelift JIT pipeline. MIR→Cranelift IR translation adapts to Kea's MIR. Cranelift integration boilerplate (builder, ISA, module setup) transfers directly. |
| rill-types         | 111 KB  | **Core extension** — Type, Row, TypeVarId, RowVarId, Substitution, Kind all transfer. Needs: EffectRow (new row kind), Unique, Ptr, fixed-width integers, @unboxed, handler types. |
| rill-actors        | 92 KB   | **Conceptual reference** — Kea actors are library-level on effects. Runtime patterns (mailbox, supervision, handle) inform kea-actors library design. No direct code transfer. |
| rill-ast           | 54 KB   | **Partial reuse** — Span, visitor patterns transfer. Node types rewritten for Kea syntax (indentation blocks, struct-everything, effect declarations, handle/resume, UMS). |
| rill-diag          | 12 KB   | **Direct reuse** — error formatting, source locations, categories. |
| rill-extension-*   | ~30 KB  | **Does not transfer** — Rill-specific extension system. |

**Lean formalization: ~1 MB total (328 KB core + 691 KB properties)**

| Module area         | Transfer status |
|---------------------|-----------------|
| Row unification (Unify, RemyPreservesLabels, UnifyExtends, UnifyReflexive, SubstBridge, SubstIdempotent, SubstCompose) | **Direct transfer** — same row algebra |
| Typing (Typing.lean, 149 KB) | **Structural transfer** — two-judgment architecture, algorithmic/declarative equivalence. Needs: effect-aware typing rules, handler typing |
| Eval (Eval.lean) | **Partial transfer** — progress/preservation scaffolding. Operational semantics differ (native vs tree-walking) |
| Traits (Traits.lean) | **Direct transfer** — coherence, supertrait closure, dispatch boundary |
| Properties (35 proofs, zero sorry) | **Mixed** — row/subst/unify proofs transfer directly. DataFrame/ColExpr proofs don't transfer. ~60% reusable |
| MCP workflow protocol | **Direct transfer** — predict/probe/classify/act methodology. Same tooling, different semantic oracle |

**Summary:** ~40% of Rill's Rust code transfers directly or with
adaptation. ~60% of the Lean formalization transfers. The biggest
wins are the row unification engine, the Cranelift pipeline, the
MCP server, and the LSP.

---

## What's Genuinely New (Not in Rill)

These are the pieces with zero codebase to cannibalise:

1. **Indentation-sensitive lexer** — INDENT/DEDENT token emission.
   Reference: Python's tokenizer, Haskell's layout rule.
   Estimated: 1 week.

2. **Algebraic effect system** — effect declarations, handler
   typing, effect row unification, handler compilation. Rill has
   purity/volatility inference but no user-defined effects or
   handlers. This is the biggest new component.
   Estimated: 2-3 weeks (type checking + compilation).

3. **Handler compilation** — CPS transform or evidence passing
   for effect handlers at runtime. This is where Kea's performance
   story lives or dies. Needs early prototyping.
   Estimated: 2 weeks for initial strategy, ongoing optimisation.

4. **Uniqueness types + borrow** — move checking pass, borrow
   parameter convention, interaction with effects and Alloc.
   Estimated: 1-2 weeks.

5. **Arena allocation as effect** — Alloc handler, escape analysis,
   deep-copy at boundary. The riskiest technical bet.
   Estimated: 2 weeks, plus formal verification.

6. **Native AOT compilation** — Rill's Cranelift path is JIT only.
   Kea needs AOT as primary target. Cranelift supports this but
   the linker integration, binary emission, and startup code are
   new work.
   Estimated: 1 week on top of existing Cranelift pipeline.

7. **Struct-everything module system** — nested types, inherent
   methods scoped to struct blocks, singleton struct modules.
   Rill uses file=module with bare declarations.
   Estimated: 1 week.

8. **UMS resolution** — method lookup (inherent → trait → qualified),
   field vs method disambiguation, `::` for qualified dispatch.
   Rill uses pipes and explicit Trait.method() calls.
   Estimated: 1 week.

---

## Implementation Phases (Revised)

### Phase 0: Bootstrap Compiler in Rust

The bootstrap compiler compiles a Kea subset to native code via
Cranelift. Written in Rust, cannibalising Rill.

**0a: Lexer + Parser (week 1)**

New: Indentation-sensitive lexer with INDENT/DEDENT tokens.
Reference: Rill's recursive descent + Pratt architecture.
Rewrite: Block handling, keywords, struct-everything nesting.

Deliverable: Parse Kea source into AST. No type checking.

**0b: Type system core (week 1-3)**

Cannibalise: rill-types (extend), rill-infer (adapt).
- Row unification for records (from Rill, direct)
- Row unification for effects (new, same algorithm)
- HM inference with let-generalisation (from Rill)
- Constraint provenance (from Rill)
- Struct-everything scoping rules (new)
- Basic trait system (from Rill)
- UMS resolution (new)
- Effect annotations: parsing and checking (new)

Deliverable: Type-check pure Kea programs with structs, enums,
pattern matching, row-polymorphic records, traits, and effect
annotations. No handlers yet. No codegen.

MCP server from day one (adapted from Rill).
Lean formalization begins: row unification (from Rill), effect
row algebra (new).

**0c: Effect handlers (week 3-4)**

New work, informed by literature (Koka, Eff, Frank).
- `effect` declaration: parsing, representation, scoping
- `handle`/`resume`: parsing, type checking
- Handler typing: effect removal and substitution
- `Fail` sugar: `?`, `fail`, `catch` desugaring
- Effect inference (bottom-up)
- Effect polymorphism (row variables on effect sets)

Deliverable: Type-check effectful Kea programs including
handlers, Fail sugar, and effect-polymorphic functions.

Lean formalization: handler typing rules, Fail desugaring
correctness, effect row operations.

**0d: Code generation — pure subset (week 4-6)**

Cannibalise: rill-codegen (Cranelift pipeline).
- Cranelift backend for pure functions
- Struct layout, enum layout (tagged unions)
- Pattern matching compilation (decision trees)
- Refcounting insertion pass
- CoW implementation for functional update (~)
- AOT binary emission (new — Rill only has JIT)
- Basic stdlib: Int, Float, String, Bool, List, Option, Result
- CLI: `kea build file.kea` → native binary

Deliverable: Compile and run pure Kea programs. No effects
at runtime yet. Pure functions, pattern matching, records,
enums work end to end.

**0e: Runtime effects (week 6-8)**

Biggest risk. Handler compilation strategy must be decided here.

Options (evaluate via benchmarking):
1. **Evidence passing** — handlers compiled as closures passed
   through the call stack. Low overhead for simple cases. Used
   by Koka for many handlers.
2. **CPS transform** — effectful code CPS-transformed, handler
   is the continuation receiver. Clean but can bloat code.
3. **Segmented stacks / setjmp** — handlers save/restore stack
   frames. Lower-level, harder to implement, potentially fastest.

Prototype all three on a microbenchmark (State effect, tight
loop) before committing. The winner becomes the compilation
strategy.

Then:
- IO effect: runtime handler providing file/network/clock
- Fail effect: compiled as Result-passing (optimised path)
- Handler compilation for user-defined effects
- `with_arena` handler: arena allocation backend
- Alloc effect: bump allocation, deep-copy at boundary
- `fn main() -[IO]> ()` as entry point

Deliverable: Effectful Kea programs compile and run. IO, error
handling, arena allocation, and user-defined effects work.

Lean formalization: handler compilation correctness (at least
for evidence passing), arena escape analysis.

**0f: Memory model (week 8-9)**

New work, informed by Austral/Clean for uniqueness.
- Unique T: move checking pass
- Borrow parameter convention (non-consuming access)
- Perceus-style reuse analysis (basic cases)
- Interaction: Unique + effects, Unique + Alloc
- Fixed-width integers, bitwise operations
- `unsafe` blocks, `Ptr T`
- `@unboxed` value types

Deliverable: Full memory model works. Performance-sensitive
code with Unique and borrow. Unsafe FFI boundary.

Lean formalization: uniqueness typing soundness, Unique/effect
interaction.

**0g: Advanced type features (week 9-11)**

Cannibalise: Rill's trait system (substantial).
- GADTs: type refinement in pattern matching
- HKTs: higher-kinded type parameters (Functor, Monad)
- Associated types
- Supertraits
- Deriving (@derive)
- Full stdlib for compiler self-hosting: Map, Set, String
  interning, file IO, command-line argument parsing, JSON
- Error messages: invest heavily (adapted from Rill's diagnostic
  infrastructure)

Deliverable: Bootstrap compiler is feature-complete enough to
compile a Kea compiler written in Kea.

### Phase 1: Self-Hosting Compiler in Kea

**1a: Port the compiler (week 11-16)**

Translate the Rust bootstrap compiler to Kea, module by module.
The bootstrap compiler compiles the Kea compiler.

This is the ultimate design validation. Every language feature
gets exercised in a real, complex program. Issues found here
are issues that would have been found by every serious user.

The compiler itself uses Kea's features:
- Effect tracking on compiler passes (-[Alloc, Fail]>)
- Handlers for compiler diagnostics (Fail → collected errors)
- Structs with inherent methods for AST nodes
- Pattern matching on IR everywhere
- Row polymorphism for compiler passes that operate on subsets
  of AST/IR node fields

Test: Kea-compiled compiler produces identical output to
Rust-compiled compiler on a comprehensive test suite.

**1b: Three-stage bootstrap (week 16-17)**

- Stage 1: Rust compiler compiles Kea compiler → binary A
- Stage 2: Binary A compiles Kea compiler → binary B
- Stage 3: Binary B compiles Kea compiler → binary C
- B and C must be identical (or semantically equivalent)
- Drop the Rust bootstrap. Kea is self-hosted.

**1c: Compiler improvements in Kea (week 17-20)**

Now iterate on the compiler using Kea itself:
- Arena allocation for IR nodes (with_arena handler)
- Unique types for in-place IR transformation
- Incremental compilation (module-level)
- Parallel compilation (actors, future)
- Optimisation passes in the Kea MIR
- Better error messages (iterate with MCP feedback loop)

### Phase 2: Tooling and Ecosystem

**2a: Essential tooling (week 20-24)**

Cannibalise heavily from Rill:
- Package manager: kea.toml, lockfile, registry (new)
- Formatter: adapted from rill-fmt (rewrite rules for
  indentation syntax)
- LSP server: adapted from rill-lsp (backend swapped to
  Kea type system, protocol layer unchanged)
- MCP server: adapted from rill-mcp (already running from
  Phase 0, polish and document)
- Test runner (new)
- REPL (new, simpler than Rill's since Kea is compiled)

**2b: Standard library (week 24-28)**

Informed by Rill's stdlib (rill-eval/src/stdlib/):
- Collections: List, Map, Set, SortedMap, SortedSet
- IO: File, Network, Stdin/Stdout (as IO effect operations)
- Text: String, Regex, JSON, TOML
- Concurrency: kea-actors library (effects + GADTs)
  - Send/Spawn effects
  - Actor trait
  - Supervision
  - Actor runtime (handler for Send/Spawn)
- Effects: kea-state, kea-log (as library effects)
- HTTP: client and server (actors + effects)
- CLI: argument parsing, terminal output

**2c: Documentation (week 28-30)**

- Getting started guide (PEDAGOGY.md layers)
- Standard library API documentation
- Effect system guide (handlers, custom effects, testing)
- Actor guide (building on effects)
- Error catalog (every compiler error with examples)
- Theory deep dive (row polymorphism, effects, handlers)

### Phase 3: Domain Libraries and Real Use

- CLI framework (first real use case — ship something useful)
- Web framework (actors + effects, typed handlers)
- Data processing library (row-polymorphic transforms)
- Agent/MCP runtime (typed tool calls, actor-per-agent)

---

## Formal Methods Strategy (Revised)

### What Transfers from Rill

The Lean formalization is a major asset. 1 MB of proven Lean 4
code, zero sorry, with a mature MCP-verified workflow.

**Direct transfer (relabel, extend):**
- Row unification: Unify.lean, UnifyExtends, UnifyReflexive,
  RemyPreservesLabels, RowFieldsSorted — same algebra for
  records AND effects
- Substitution: Substitution.lean, SubstBridge, SubstIdempotent,
  SubstCompose — applies to both type vars and effect vars
- Typing core: Typing.lean (149 KB!) — two-judgment architecture
  (HasType + HasTypeU), algorithmic soundness, determinism.
  Needs effect-aware extension but scaffolding transfers.
- Trait coherence: Traits.lean — orphan rule, supertrait closure,
  dispatch boundary

**Needs new formalisation:**
- Effect row operations (add/remove effect from row)
- Handler typing (effect removal + substitution)
- Handler compilation correctness
- Uniqueness typing (linear use, borrow safety)
- Arena escape analysis (highest risk)
- GADT refinement in pattern matching

### Formalisation Priority Order

1. **Row unification for effects** — extends existing proofs.
   Must be done first because everything depends on it.
2. **Handler typing rules** — novel, needs verification. The
   "handle removes E, adds H" rule must be proven sound.
3. **Arena escape analysis** — highest-risk bet. If this has
   a soundness hole, major redesign needed. Formal backing
   is essential.
4. **Uniqueness/borrow interaction with effects** — must not
   have soundness holes. Unique values crossing handler
   boundaries is the tricky case.
5. **GADT refinement** — known tricky. Existing literature
   helps but Kea-specific interaction with effects needs proof.
6. **Handler compilation correctness** — prove the chosen
   compilation strategy preserves semantics.

### MCP-First Workflow

Same protocol as Rill. The compiler's MCP server is the oracle:

1. **Predict**: state the Lean-side conjecture.
2. **Probe**: run MCP checks (happy, boundary, adversarial).
3. **Classify**: agreement, precondition gap, or divergence.
4. **Act**: prove, revise, or log divergence.
5. **Traceability**: link theorems, edits, MCP evidence.

False theorem discovery is the most valuable output. The effect
handler typing rules and arena escape analysis are where the
false theorems are hiding.

---

## Agentic Workflow Strategy

### Agent Allocation by Phase

| Phase | Strategy | Agents | Rationale |
|-------|----------|--------|-----------|
| 0a    | Tight pairing | 1-2 | Parser needs coherent indentation design |
| 0b    | Tight pairing | 1-2 | Type system core needs unified vision |
| 0c    | Tight pairing | 1-2 | Effect handlers need coherent design |
| 0d    | Parallel | 3-5 | Codegen for different node types is independent |
| 0e    | Prototype + decide | 2-3 | Three handler strategies prototyped in parallel, then converge |
| 0f    | Tight pairing | 1-2 | Memory model needs coherent design |
| 0g    | Mixed | 2-4 | Traits are coherence-sensitive; stdlib is parallelisable |
| 1a    | Tight pairing | 1-2 | Porting compiler is high-coherence |
| 1b    | Single | 1 | Bootstrap verification is sequential |
| 2a    | Parallel | 4-6 | Every tool is independent |
| 2b    | Parallel | 4-6 | Stdlib modules are independent |
| 2c    | Parallel | 3-4 | Documentation is independent |

### What Makes Agentic Bootstrap Work

Learned from Rill:

1. **KERNEL spec is the source of truth.** Agents read it. When
   the spec is wrong, fix the spec, not the agent's interpretation.
2. **MCP server from day one.** Agents test against it. The
   formalization tests against it. Human tests against it. One
   feedback loop for everyone.
3. **Lean formalization in parallel.** False theorems catch design
   bugs before they become implementation bugs.
4. **Test suite is ground truth.** Every feature gets tests before
   implementation. The test suite is the contract.
5. **Comprehensive property tests.** Rill's 166 KB of property
   tests in rill-infer caught bugs that unit tests missed.

---

## Timeline Summary

| Phase | Weeks  | Deliverable |
|-------|--------|-------------|
| 0a    | 1      | Parser (indentation-sensitive) |
| 0b    | 1-3    | Type system core (records, effects, rows, traits) |
| 0c    | 3-4    | Effect handlers, Fail sugar |
| 0d    | 4-6    | Cranelift codegen, pure programs run natively |
| 0e    | 6-8    | Runtime effects (IO, Fail, handlers, arenas) |
| 0f    | 8-9    | Memory model (Unique, borrow, unsafe) |
| 0g    | 9-11   | GADTs, HKTs, full stdlib, error messages |
| 1a    | 11-16  | Compiler ported to Kea |
| 1b    | 16-17  | Three-stage bootstrap proven |
| 1c    | 17-20  | Compiler improvements in Kea |
| 2a    | 20-24  | Tooling (pkg mgr, LSP, formatter, MCP) |
| 2b    | 24-28  | Standard library |
| 2c    | 28-30  | Documentation |
| 3     | 30+    | Domain libraries |

Self-hosting at week 17. Usable by others at week 30.

With Rill's codebase to cannibalise and aggressive agentic
parallelism, this could compress to ~70% of estimates
(self-hosting ~week 12, usable ~week 21).

---

## Risk Register

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Handler compilation too slow for hot paths | Medium | High | Prototype 3 strategies early (0e); benchmark before committing |
| Arena escape analysis unsound | Medium | High | Lean formalization (priority 3); design fallback without arenas |
| Indentation parser harder than expected | Low | Medium | Python/Haskell as proven references; well-understood problem |
| Self-hosting reveals design flaws late | Medium | Medium | MCP + Lean catch bugs early; self-hosting is validation not discovery |
| Uniqueness + effects interaction unsound | Low | High | Lean formalization (priority 4) |
| Row unification for effects diverges from records | Low | High | Same algorithm, proven in Rill; extend proofs first |
| Nobody uses it | High | Terminal | Ship CLI tool early; get feedback; don't over-design |
| Rill codebase too entangled to cannibalise | Low | Medium | Copy + adapt, don't try to abstract; clean break |
