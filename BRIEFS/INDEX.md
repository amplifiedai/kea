# Kea Workboard

Single source of truth for project work status. Read this first to know what's happening.

See `AGENTS.md` > "Briefs and Workboard" for how to manage this file.

---

## Cross-Cutting Requirements

**Read these before implementing any phase.** These briefs define constraints
that apply across multiple implementation phases. Ignoring them means rework.

| Brief | Applies to | Key constraints |
|-------|-----------|-----------------|
| [Performance and backend strategy](design/performance-backend-strategy.md) | **0d, 0d1, 0e, 0f** | MIR must be backend-neutral (not shaped around Cranelift). Backend interface trait. ABI manifest artifact. Pass stats. Layout stability (declaration order = memory order). Actor benchmark targets. Reuse analysis is a MIR pass (0f). |
| [Testing](todo/testing.md) | **0d+** | Benchmark harness is a 0d Definition of Done item. Test runner design (assert/check model) informs how test infrastructure is built. |
| [Semantic introspection platform](design/runtime-introspection-mcp.md) | **0b-0d1** | Compiler MCP contracts must be maintained as new phases land. kea-mcp already exists — new type/effect features must be queryable. 0d1's compilation API extraction is the foundation for "one engine, many consumers." |
| [Lean formalization](in-progress/lean-formalization.md) | **0c, 0d, 0e** | Formal agent runs in parallel. Core type system migration starts after 0c. Effect typing proofs run alongside 0d/0e. Don't break the MCP interface the formal agent uses. |
| [Tooling and DX](design/tooling-dx.md) | **0a through Phase 2** | Everything ships in one `kea` binary. Formatter lands before 0g. LSP by 0d-0e. `kea test`, `kea fmt`, `kea build`, `kea run` are non-negotiable. Effect-aware documentation and diagnostics. Every new feature must be queryable via tooling. |
| [Error message quality](todo/0h-stdlib-errors.md) | **0g, 0f** | Every new type/effect feature ships with snapshot-tested diagnostics. No unification variables in user-facing errors. Row-diff errors for records and effects. Effect provenance traces. 0h is not on the critical path but its design principles are cross-cutting — see 0g §Cross-Cutting: Error Message Quality. |

---

## Active

Work in progress right now. Each entry should have a `## Progress` section in its brief.
- **[Stdlib bootstrap](in-progress/stdlib-bootstrap.md)** — Active. Tier-0 bootstrap started with real repo stdlib modules (`prelude`, `option`, intrinsic-backed `text`) and execute-path module-system coverage; remaining Tier-0 pure modules (`int`, `float`, `order`, `eq`, `ord`, `show`) are next, while heap-list `List` stays explicitly blocked on runtime/list-lowering support.
- **[Memory model](in-progress/0f-memory-model.md)** — Active. Steps 1-2 (move checking, borrow checking) done. Step 3a (release scheduling, churn fusion, linear alias transfer) done. Step 6 (fixed-width integers, bitwise ops, numeric inference, layout intrinsics) largely done. **Step 3 expanded** with five new sub-steps based on Lean 4/Koka/Perceus research: 3b auto borrow inference, 3c drop specialisation, 3d reuse tokens (FBIP), 3e TRMC, 3f FIP verification. Next: Step 3b (auto borrow inference — single highest-impact optimisation).
- **[Lean formalization](in-progress/lean-formalization.md)** — Active. Phase 1 kickoff started from the Rill Lean baseline; next is Kea effect-row alignment in core modules/proofs.
- **[Practical language gaps](in-progress/practical-language-gaps.md)** — Active. Gaps 6-8 (IO decomposition, mutual recursion, enum keyword) are done; remaining high-priority work is Gaps 1-3 (layout intrinsics, numeric inference, string ops) for self-hosting.

---

## Ready

Designed and approved. Ready to pick up. Ordered by execution sequence per ROADMAP.md phases.

### Phase 0a: Lexer + Parser (week 1)

*(done — see Done section)*

### Phase 0b: Type System Core (weeks 1-3)

*(done — see Done section)*

### Phase 0c: Effect Handlers (weeks 3-4)

*(done — see Done section)*

### Phase 0d: Code Generation — Pure Subset (weeks 4-6)

*(done — see Done section)*

### Phase 0d1: Module System + Stdlib Tier 0 (after 0d)

*(in progress — see Active section)*

### Phase 0e: Runtime Effects + Stdlib Tier 1 (after 0d1)

*(done — see Done section)*

### Phase 0f: Memory Model + Stdlib Tier 2 (steps 1-6 need 0d, step 7 needs 0e)

*(in progress — see Active section)*

### Phase 0g: Advanced Types + @derive + Stdlib Tier 3 (needs 0d + 0c)

10. **[Advanced type features](todo/0g-advanced-types.md)** — GADTs, Eff kind, associated types, supertraits, @derive(Show, Eq, Ord). Stdlib Tier 3: Foldable, Iterator, JSON, sorted collections. **0g completion = stdlib sufficient for self-hosting.**

### Phase 0h: Error Message Quality (parallel, not blocking)

11. **[Error message quality](todo/0h-stdlib-errors.md)** — Row-diff error messages, effect provenance in diagnostics, stable error codes, snapshot tests. Not on critical path — runs in parallel with 0g.

### Cross-phase: Practical Language Gaps (0f through Phase 1)

*(moved to Active — see above)*

### Post-0e syntax

*(done — see Done section)*

### Parallel tracks

14. **[Idiomatic stdlib pass](todo/idiomatic-stdlib-pass.md)** (after Tier 0 blockers, parallel) — Quality pass on all stdlib modules: Fail-over-Result signatures, Elixir/Rust-quality doc comments, naming consistency, remove Result monadic combinators. Establishes the quality bar for all future stdlib.
15. **[Adversarial test pass](todo/adversarial-test-pass.md)** (0a–0e, parallel) — Systematic sad-path and edge-case coverage across all completed phases. Malformed syntax, type system edge cases, effect scoping violations, handler misuse, codegen correctness, runtime effect interactions. No compiler panics on any input.
7. **[Testing](todo/testing.md)** (Phase 0d through Phase 1) — `assert` (Fail) + `check` (Test effect) dual assertion model. Compiler-level expression capture, structural diff, effect-driven parallelism, property testing via `Gen` effect. Test runner portion starts with 0d. Benchmark harness is a 0d deliverable.
8. **[Lean formalization](in-progress/lean-formalization.md)** (Phase 0c-0e parallel, active) — Migrate Rill's Lean 4 formalization into Kea, then prove Kea-specific effect handler properties (removal, resume linearity, Fail/Result equivalence).
12. **[Algorithm gallery](todo/algorithm-gallery.md)** (Phase 0e through 0g, parallel) — Curated corpus of classic algorithms in `tests/algorithms/`. Exemplary code with doc comments, test blocks, and CI benchmarks. Validates language features per phase: Welford's (0e), FNV-1a + merge sort (0f early), quicksort + HAMT (0f mid-late), UTF-8 validation + KMP (0g).

### Phase 1: Self-Hosting Compiler

16. **[Phase 1a: FFI](todo/phase-1a-ffi.md)** — Foreign function interface as a language feature. `@extern("c")`, `unsafe` blocks, `Ptr T` operations, `@link` for static linking, C type aliases, String/Bytes interop. Cranelift bindings (`cranelift.kea`) as validation. Sets the pattern for every C library integration.
17. **[Phase 1b/1c: Compiler in Kea + Bootstrap](todo/phase-1bc-compiler-in-kea.md)** — Pass-by-pass translation of the compiler from Rust to Kea (lexer → parser → name resolution → type inference → MIR → optimisation → codegen → driver). Three-stage bootstrap proves correctness, drops Rust.
18. **[Phase 1d: Compiler improvements](todo/phase-1d-compiler-improvements.md)** — Incremental compilation (Query effect, sub-100ms rebuilds), parallel passes (Par.map on pure passes), arena-scoped phases (Alloc effect), error message investment (row-diff, effect provenance, stable codes).

### Phase 2-3: Not yet briefed

See ROADMAP.md for details. Briefs will be written as Phase 1 progresses.

---

## Design

Needs more design work. Briefs exist but aren't implementation-ready.

### Early tooling (parallel track, weeks 2-6)

- **Formatter** (`kea fmt`) — indentation-sensitive language needs a formatter before serious code is written. Reuse rill-fmt's doc algebra + comment infra (~440 LOC transfers). Rewrite printer + rules for indent-sensitive output. Lands before 0g.
- **Basic LSP** — hover types, go-to-def, diagnostics. Adapted from rill-lsp (protocol layer unchanged). Lands by 0d-0e.

### Other design work

- **[Serialization](design/serialization.md)** (Phase 2) — Type-driven Encode/Decode with Validated error accumulation, row-polymorphic partial deserialization, format-agnostic FormatWriter/FormatReader traits. Adapted from Rill's Format brief.
- **[Performance and backend strategy](design/performance-backend-strategy.md)** (Phase 0d-3 cross-cutting) — Define measurable performance targets and design MIR/ownership/effect IR now so future LLVM/native backend paths are possible without re-architecting the compiler core.
- **[Semantic introspection platform](design/runtime-introspection-mcp.md)** (Phase 0b-2 cross-cutting) — One semantic engine for many consumers (LSP, REPL, debugger, CI, agents). Hard split between compiler MCP (dev-time rich surface) and runtime introspection (policy-gated capability effect with bounded/audited responses).
- **Supervision trait API + mailbox configuration** — How exactly does the `Supervisor` trait work? KERNEL §19.5 sketches it loosely. Needs concrete trait definition for kea-actors. Also: mailbox config at spawn time — `Spawn.spawn(actor, config: { mailbox: Bounded 1000 })`. Backpressure is a mailbox property (receiver-side), not an effect handler (sender-side). `Send.tell` stays a direct runtime call per §5.15; the mailbox type determines full-queue behavior (block/error/drop). Depends on Actor trait (§19.3) being implemented.
- **[Distributed actors](design/distributed-actors.md)** (Phase 2-3) — Location-transparent `Ref`, remote proxy handles (no distributed refcounting), `Encode` constraint at node boundary, monitoring/links, supervision. `Send` remains a capability effect with runtime transport decision (local vs remote). Typed OTP-style guarantees. Depends on local actors (0e), serialization, GADTs (0g).
- **[Tooling and DX](design/tooling-dx.md)** (Phase 0 parallel through Phase 2) — Go-style blessed tooling in one binary. Zero-config formatter, built-in test runner, effect-aware documentation, effect badges in package registry. Everything in `kea`.
- **[Packaging, FFI, and comptime](design/packaging-ffi-comptime.md)** (Phase 1-2) — C FFI via `extern "C"`, Arrow as library package, package registry with effect-based permissions, no install/build scripts, comptime via `Compile` effect (compiler layer interface as code generation). `@derive` transitions from hardcoded pass to comptime function.
- **[Package registry](design/package-registry.md)** (Phase 0 through Phase 2) — Three-phase registry strategy: Phase 0 Git dependencies (`kea.toml` + `kea.lock`), Phase 1 hosted registry with effect-aware metadata (effect badges, effect diff on version bumps, transparency log, OIDC publishing), Phase 2 effect policies (`[policy]` in kea.toml, `kea pkg audit`). Open questions: flat vs namespaced naming, hosting model, native deps.
- **[Typed grammar interface](design/typed-grammar-interface.md)** (Phase 1-2) — One universal typed embedding path (`embed <Grammar> { ... }`) for HTML/SQL/CSS/Einsum-style blocks, implemented as comptime extensions using `Compile` capabilities. Domain sugars (`html {}`) desugar to the same core mechanism.
- **[IR–Recipes–Grammar convergence](design/ir-recipes-grammar-convergence.md)** (Phase 1-2) — Grammars, recipes (KERNEL §15), and backends are the same mechanism: compile-time functions under decomposed compilation effects (`Parse`, `TypeCheck`, `Lower`, `Diagnose`) that transform typed IR. StableHIR is row-extensible for forward-compatible recipes. Restricted sublanguages (§15.2) ARE grammars. Backends ARE grammar implementations over MIR. Connects typed-grammar-interface, packaging-ffi-comptime, and performance-backend-strategy.
- **[Revision-preserving evolution](design/revision-preserving-evolution.md)** (Phase 2+, post-v1) — Row polymorphism handles additive changes (new nodes/fields). Version tags handle breaking changes. Revisions handle the third category: widening existing field types without breaking consumers. Inspired by Dashbit/Valim’s set-theoretic data evolution. General language mechanism, not compiler-specific. Genuinely novel PL research combining row polymorphism with revision preservation.
- **[Live code loading](design/live-code-loading.md)** (Phase 0d+ through Phase 3) — Three tiers: REPL/script dependency loading (`Pkg.install`, `@install`), dev-mode hot reload via Cranelift JIT hotswap (`kea run --watch`), and speculative production actor hot reload. Effect-checked compatibility on reload. Not dlopen — Kea source compiled through full pipeline.
- **[Effects as platform](design/effects-platform-vision.md)** (Phase 0e-1 design, Phase 2-3 features) — Platform capabilities Kea's effect system unlocks: policy-as-code (policy violations = type errors), deterministic simulation via record/replay, safe plugin ecosystems, ambient context without globals, portable execution substrates, structurally derived observability, agent-native APIs. Defines IO decomposition requirement (IO vs Net vs Clock vs Rand as separate capability effects).
- **[Self-hosting compiler performance](design/self-hosting-perf.md)** (Phase 1-2) — Why the self-hosted compiler is the perfect workload for Kea's memory model: Unique IR pipeline (zero RC), arena-scoped phases (bump allocation), effect-tracked parallel passes (Sorbet-style), Salsa-style incremental queries via Query effect. Performance targets: <20% memory overhead (vs OCaml's 90%), 100K+ lines/sec/core type checking, sub-100ms incremental rebuilds. Captures the compound advantage of Perceus + Unique + effects.
- **Arena allocation semantics** — `Alloc` effect, deep-copy at boundary, interaction with Unique. KERNEL §12.7 specifies behavior; implementation strategy is the open question. Partially covered in 0e and 0f briefs.

---

## Done (recent)

Completed briefs. Kept for reference and design rationale.

| Brief | Summary |
|-------|---------|
| [syntax-migration](done/syntax-migration-rill-to-kea.md) | Rill→Kea syntax migration complete: `struct` (with `record` deprecated), `base~{ field }` functional update, `(a, b)` tuples (with `#()` deprecated), `%{}` map literals verified. |
| [string-interpolation](done/string-interpolation.md) | KERNEL §1.6 landed with `{...}` interpolation, escaped braces (`{{`/`}}`), parser desugaring to `show(...)` + concat, and CLI/runtime regression coverage. |
| [`with` syntax](done/with-syntax.md) | Callback-flattening sugar landed end-to-end: `with`/`with pat <- ...` parsing, `@with` parameter annotations, AST/HIR/typechecker desugaring, target validation diagnostics, block-order lint warning (`W0902`), and parser/infer/CLI regression coverage. |
| [0d-codegen-pure](done/0d-codegen-pure.md) | Pure-subset codegen landed end-to-end (HIR→MIR→Cranelift, JIT+AOT, closure/RC/runtime lowering coverage), with 0d punch-list closeout complete; evaluator-parity snapshot corpus is explicitly deferred and blocked on future `kea-eval` infrastructure. |
| [0d1-module-system](done/0d1-module-system.md) | Module resolver/import DAG/prelude/matrix/compiler-API extraction are done, with real repo `stdlib/` modules in-tree and execute-path integration proving module imports plus intrinsic-backed stdlib calls (`Option.unwrap_or` + `Text.length`) end-to-end. Heap-list stdlib remains deferred to stdlib-bootstrap/runtime support. |
| [0e-runtime-effects](done/0e-runtime-effects.md) | Runtime effects landed end-to-end: Fail/ZeroResume Result path, direct capability effects (IO/Net/Clock/Rand), tail-resumptive user handlers (`State`/`Log`/`Reader`) with nesting/scoping + `then`, pass-stat visibility, and benchmark + CI gates validated (`check-full`, regression benchmarks green). |
| [0e-remedy](done/0e-remedy.md) | Post-0e runtime correctness and infra gaps closed: multi-operation handler cell bug fixed, JIT IO/Net shims made real, AOT runtime shim linkage added, Clock now/monotonic routed through explicit runtime symbols, parser `$` wording corrected, test runner compile-once iterations implemented, and HIR caching added to compilation context. |
| [const-fields](done/const-fields.md) | `const` fields are complete for Phase 0 strict subset: parser/AST/typecheck const declarations, const dependency cycle checks, qualified const access lowering, and `Type.name` const pattern matching lowered to equality checks with regression coverage. Heap static-data placement/evaluator parity is explicitly deferred to later runtime/evaluator work. |
| [0b-rill-surface-cleanup](done/0b-rill-surface-cleanup.md) | Removed remaining inherited non-Kea parser/typechecker substrate from core crates (frame token path, stale infer trace variants, and `sqlparser`), with cleanup gates green across check/test/check-full. |
| [0b-mcp-server](done/0b-mcp-server.md) | `kea-mcp` now exposes `type_check`, `diagnose`, and `get_type` over MCP stdio with structured JSON diagnostics from serializable `kea-diag` types. |
| [0b-type-system-core](done/0b-type-system-core.md) | Type checker migrated to row-native effect contracts/unification with lattice model deleted, legacy effect syntax deprecation-only, fail-row constraints enforced, and stable module namespace resolution scaffolding for builtin/source transitions. |
| [0c-effect-handlers](done/0c-effect-handlers.md) | Effect declarations, `handle`/`resume` typing, and `fail`/`?`/`catch` desugaring landed with row-native effect removal checks and at-most-once resume enforcement. Follow-up tooling debt: add explicit MCP regressions for effect/handler query flows. |
| [0a-lexer-parser](done/0a-lexer-parser.md) | Indentation-sensitive lexer/parser landed with indentation-only block parsing, snapshot corpora, and property tests for layout/error coherence. |
| [benchmark-infrastructure](done/benchmark-infrastructure.md) | Divan harness with AllocProfiler, CodSpeed CI (OIDC), Stage A/B regression gates, whole-program corpus (hyperfine), variance characterization, optimization contract verification, stable blocking lanes. |
| [syntax-grammars](done/syntax-grammars.md) | Tree-sitter grammar (flat, 8 GLR conflicts, parses 16 stdlib + 13/15 test files), effect-aware highlight queries, TextMate grammar (Linguist-ready), Neovim/Helix/VS Code editor configs, 35-test corpus. |
| [bootstrap-infra](done/bootstrap-infra.md) | Cargo workspace, mise tasks, scripts, BRIEFS system, docs, .claude setup. Cannibalised from rill. |

---

## Dependency Graph

```
0a: lexer + parser                                           ← DONE
 └── 0b: type system core                                    ← DONE
      └── 0c: effect handlers                                ← DONE
           │
           └── 0d: codegen pure                                    ← DONE
                │
                ├── 0d1: module system + STDLIB TIER 0 (pure)
                │    │   (use/import, prelude, Option/Result/List/String as .kea)
                │    │
                │    ├── 0e: runtime effects + STDLIB TIER 1 (effects)  ← DONE
                │    │    │   (IO/State/Log as .kea, handler tests in Kea)
                │    │    │
                │    │    └── 0f step 7: Unique + effects
                │    │
                │    ├── 0f steps 1-6 + STDLIB TIER 2 (performance)
                │    │    (Vector/HAMT Map/Set as .kea using Ptr/@unsafe)
                │    │
                │    └── 0g + @derive + STDLIB TIER 3 (abstractions)
                │         (Foldable/Iterator/JSON/sorted collections as .kea)
                │         │
                │         └── Phase 1a: FFI + Cranelift bindings
                │              └── Phase 1b/1c: compiler in Kea + bootstrap
                │                   └── Phase 1d: incremental, parallel, arenas, errors
                │
                ├── 0h: error message quality (parallel, not blocking)
                │
                ├── lean formalization phase 2 (parallel)
                ├── testing: benchmark harness + test runner (parallel)
                └── semantic introspection platform (cross-cutting)

Parallelism after 0d1 lands:
  0e ──────────┐
  0f steps 1-6 ├── can all run concurrently
  0g ──────────┘
  0h ── parallel track (not blocking self-hosting)
  lean, testing ── parallel tracks throughout

Critical path to "hello world compiles":  0d → 0d1 → 0e (IO handler)
Critical path to self-hosting:            0d → 0d1 → 0g → Phase 1
(0h removed from critical path)

Cross-cutting (read before implementing any phase):
  performance-backend-strategy.md  → 0d, 0e, 0f
  testing.md                       → 0d+
  runtime-introspection-mcp.md     → 0b-0d
  lean-formalization.md            → 0c, 0d, 0e (parallel)
  tooling-dx.md                    → 0a through Phase 2
```
