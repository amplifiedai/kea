# Kea Workboard

Single source of truth for project work status. Read this first to know what's happening.

See `AGENTS.md` > "Briefs and Workboard" for how to manage this file.

---

## Cross-Cutting Requirements

**Read these before implementing any phase.** These briefs define constraints
that apply across multiple implementation phases. Ignoring them means rework.

| Brief | Applies to | Key constraints |
|-------|-----------|-----------------|
| [Performance and backend strategy](design/performance-backend-strategy.md) | **0d, 0e, 0f** | MIR must be backend-neutral (not shaped around Cranelift). Backend interface trait. ABI manifest artifact. Pass stats. Layout stability (declaration order = memory order). Actor benchmark targets. Reuse analysis is a MIR pass (0f). |
| [Testing](todo/testing.md) | **0d+** | Benchmark harness is a 0d Definition of Done item. Test runner design (assert/check model) informs how test infrastructure is built. |
| [Semantic introspection platform](design/runtime-introspection-mcp.md) | **0b-0d** | Compiler MCP contracts must be maintained as new phases land. kea-mcp already exists — new type/effect features must be queryable. |
| [Lean formalization](in-progress/lean-formalization.md) | **0c, 0d, 0e** | Formal agent runs in parallel. Core type system migration starts after 0c. Effect typing proofs run alongside 0d/0e. Don't break the MCP interface the formal agent uses. |
| [Tooling and DX](design/tooling-dx.md) | **0a through Phase 2** | Everything ships in one `kea` binary. Formatter lands before 0g. LSP by 0d-0e. `kea test`, `kea fmt`, `kea build`, `kea run` are non-negotiable. Effect-aware documentation and diagnostics. Every new feature must be queryable via tooling. |

---

## Active

Work in progress right now. Each entry should have a `## Progress` section in its brief.
- **[Codegen — pure subset](in-progress/0d-codegen-pure.md)** — Active. Step 0 structural function-effect embedding is complete; Step 1 (`kea-hir`) and Step 2 (`kea-mir`) include real pure-path lowering for literals/vars/unary/binary/call/let/block plus Unit/value `if` control-flow graphs; bool and simple literal+wildcard `case` lower to canonical `if` in HIR. Step 3 performs real pure-subset MIR→Cranelift lowering with host JIT + AOT object emission, including block params/Jump args for value-producing control flow; Step 7 now has a `kea` CLI scaffold (`run`/`build`) wired through the pipeline with executable linking in `build` and runnable compiled execution in `run` (temporary link path).
- **[Lean formalization](in-progress/lean-formalization.md)** — Active. Phase 1 kickoff started from the Rill Lean baseline; next is Kea effect-row alignment in core modules/proofs.

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

*(active — see Active section)*

### Phase 0e: Runtime Effects (weeks 6-8)

6. **[Runtime effects](todo/0e-runtime-effects.md)** — Handler compilation strategy (evidence passing vs CPS vs segmented stacks), tail-resumptive optimisation, handler inlining/devirtualization, IO runtime, Fail optimised path, arena allocation. Highest risk phase. **Also read:** [performance-backend-strategy](design/performance-backend-strategy.md) (effect ops as classified MIR ops, handler benchmark gates).

### Phase 0f: Memory Model (parallel with 0e, steps 1-5 only need 0d)

9. **[Memory model](todo/0f-memory-model.md)** — Unique T (move semantics), borrow convention, reuse analysis (pure optimisation), unsafe/Ptr, @unboxed, fixed-width integers. Steps 1-5 only need 0d codegen. Step 6 (Unique + effects) needs 0e. Type-driven optimisation: Unique gives guaranteed single ownership → unconditional in-place mutation. Reuse analysis uses type info to prove refcount==1.

### Phase 0g: Advanced Types (parallel with 0f, only needs 0d + 0c)

10. **[Advanced type features](todo/0g-advanced-types.md)** — GADTs (typed actor protocols), Eff kind (effect-parameterised types), associated types, supertraits. Pure type theory — no dependency on memory model. GADTs enable `CounterMsg T` typed protocols. Eff kind enables `Server E` effect-polymorphic types.

### Phase 0h: Stdlib, Deriving, Error Messages (needs 0g)

11. **[Stdlib, deriving, and error messages](todo/0h-stdlib-errors.md)** — @derive, effects-first stdlib (stdlib IS the effect vocabulary), row-diff error messages (structural missing/extra for records and effects), effect provenance in diagnostics. The most exciting phase: where effects stop being a language feature and become the API design principle.

### Parallel tracks

7. **[Testing](todo/testing.md)** (Phase 0d through Phase 1) — `assert` (Fail) + `check` (Test effect) dual assertion model. Compiler-level expression capture, structural diff, effect-driven parallelism, property testing via `Gen` effect. Test runner portion starts with 0d. Benchmark harness is a 0d deliverable.
8. **[Lean formalization](in-progress/lean-formalization.md)** (Phase 0c-0e parallel, active) — Migrate Rill's Lean 4 formalization into Kea, then prove Kea-specific effect handler properties (removal, resume linearity, Fail/Result equivalence).

### Phase 1-3: Not yet briefed

See ROADMAP.md for details. Briefs will be written as earlier phases complete.

---

## Design

Needs more design work. Briefs exist but aren't implementation-ready.

### Early tooling (parallel track, weeks 2-6)

- **Tree-sitter grammar** — standalone, no compiler dependency. Syntax highlighting in every editor. Can start now (0a is done, syntax is stable).
- **Formatter** (`kea fmt`) — indentation-sensitive language needs a formatter before serious code is written. Reuse rill-fmt's doc algebra + comment infra (~440 LOC transfers). Rewrite printer + rules for indent-sensitive output. Lands before 0g.
- **Neovim plugin** — tree-sitter highlighting + LSP client config. After tree-sitter grammar + basic LSP.
- **Basic LSP** — hover types, go-to-def, diagnostics. Adapted from rill-lsp (protocol layer unchanged). Lands by 0d-0e.

### Other design work

- **[Serialization](design/serialization.md)** (Phase 2) — Type-driven Encode/Decode with Validated error accumulation, row-polymorphic partial deserialization, format-agnostic FormatWriter/FormatReader traits. Adapted from Rill's Format brief.
- **[Benchmark infrastructure](design/benchmark-infrastructure.md)** (0d deliverable) — divan + CodSpeed + iai-callgrind. Allocation counting, CI regression gates, optimization contract verification. Prerequisite for performance-backend-strategy gates.
- **[Performance and backend strategy](design/performance-backend-strategy.md)** (Phase 0d-3 cross-cutting) — Define measurable performance targets and design MIR/ownership/effect IR now so future LLVM/native backend paths are possible without re-architecting the compiler core.
- **[Semantic introspection platform](design/runtime-introspection-mcp.md)** (Phase 0b-2 cross-cutting) — One semantic engine for many consumers (LSP, REPL, debugger, CI, agents). Hard split between compiler MCP (dev-time rich surface) and runtime introspection (policy-gated capability effect with bounded/audited responses).
- **Supervision trait API + mailbox configuration** — How exactly does the `Supervisor` trait work? KERNEL §19.5 sketches it loosely. Needs concrete trait definition for kea-actors. Also: mailbox config at spawn time — `Spawn.spawn(actor, config: { mailbox: Bounded 1000 })`. Backpressure is a mailbox property (receiver-side), not an effect handler (sender-side). `Send.tell` stays a direct runtime call per §5.15; the mailbox type determines full-queue behavior (block/error/drop). Depends on Actor trait (§19.3) being implemented.
- **[Distributed actors](design/distributed-actors.md)** (Phase 2-3) — Location-transparent `Ref`, remote proxy handles (no distributed refcounting), `Encode` constraint at node boundary, monitoring/links, supervision. `Send` remains a capability effect with runtime transport decision (local vs remote). Typed OTP-style guarantees. Depends on local actors (0e), serialization, GADTs (0g).
- **[Tooling and DX](design/tooling-dx.md)** (Phase 0 parallel through Phase 2) — Go-style blessed tooling in one binary. Zero-config formatter, built-in test runner, effect-aware documentation, effect badges in package registry. Everything in `kea`.
- **[Packaging, FFI, and comptime](design/packaging-ffi-comptime.md)** (Phase 1-2) — C FFI via `extern "C"`, Arrow as library package, package registry with effect-based permissions, no install/build scripts, comptime via `Compile` effect (compiler layer interface as code generation). `@derive` transitions from hardcoded pass to comptime function.
- **[Typed grammar interface](design/typed-grammar-interface.md)** (Phase 1-2) — One universal typed embedding path (`embed <Grammar> { ... }`) for HTML/SQL/CSS/Einsum-style blocks, implemented as comptime extensions using `Compile` capabilities. Domain sugars (`html {}`) desugar to the same core mechanism.
- **[IR–Recipes–Grammar convergence](design/ir-recipes-grammar-convergence.md)** (Phase 1-2) — Grammars, recipes (KERNEL §15), and backends are the same mechanism: compile-time functions under `Compile` effect that transform typed IR. StableHIR is row-extensible for forward-compatible recipes. Restricted sublanguages (§15.2) ARE grammars. Backends ARE grammar implementations over MIR. Connects typed-grammar-interface, packaging-ffi-comptime, and performance-backend-strategy.
- **[Live code loading](design/live-code-loading.md)** (Phase 0d+ through Phase 3) — Three tiers: REPL/script dependency loading (`Pkg.install`, `@install`), dev-mode hot reload via Cranelift JIT hotswap (`kea run --watch`), and speculative production actor hot reload. Effect-checked compatibility on reload. Not dlopen — Kea source compiled through full pipeline.
- **[Effects as platform](design/effects-platform-vision.md)** (Phase 0e-1 design, Phase 2-3 features) — Platform capabilities Kea's effect system unlocks: policy-as-code (policy violations = type errors), deterministic simulation via record/replay, safe plugin ecosystems, ambient context without globals, portable execution substrates, structurally derived observability, agent-native APIs. Defines IO decomposition requirement (IO vs Net vs Clock vs Rand as separate capability effects).
- **Arena allocation semantics** — `Alloc` effect, deep-copy at boundary, interaction with Unique. KERNEL §12.7 specifies behavior; implementation strategy is the open question. Partially covered in 0e and 0f briefs.

---

## Done (recent)

Completed briefs. Kept for reference and design rationale.

| Brief | Summary |
|-------|---------|
| [0b-rill-surface-cleanup](done/0b-rill-surface-cleanup.md) | Removed remaining inherited non-Kea parser/typechecker substrate from core crates (frame token path, stale infer trace variants, and `sqlparser`), with cleanup gates green across check/test/check-full. |
| [0b-mcp-server](done/0b-mcp-server.md) | `kea-mcp` now exposes `type_check`, `diagnose`, and `get_type` over MCP stdio with structured JSON diagnostics from serializable `kea-diag` types. |
| [0b-type-system-core](done/0b-type-system-core.md) | Type checker migrated to row-native effect contracts/unification with lattice model deleted, legacy effect syntax deprecation-only, fail-row constraints enforced, and stable module namespace resolution scaffolding for builtin/source transitions. |
| [0c-effect-handlers](done/0c-effect-handlers.md) | Effect declarations, `handle`/`resume` typing, and `fail`/`?`/`catch` desugaring landed with row-native effect removal checks and at-most-once resume enforcement. Follow-up tooling debt: add explicit MCP regressions for effect/handler query flows. |
| [0a-lexer-parser](done/0a-lexer-parser.md) | Indentation-sensitive lexer/parser landed with indentation-only block parsing, snapshot corpora, and property tests for layout/error coherence. |
| [bootstrap-infra](done/bootstrap-infra.md) | Cargo workspace, mise tasks, scripts, BRIEFS system, docs, .claude setup. Cannibalised from rill. |

---

## Dependency Graph

```
0a: lexer + parser                                           ← DONE
 └── 0b: type system core                                    ← DONE
      └── 0c: effect handlers                                ← DONE
           │
           └── 0d: codegen pure ◄─── ACTIVE
                │
                ├── 0e: runtime effects (handler compilation, IO)
                │    │
                │    └── 0f step 6: Unique + effects interaction
                │
                ├── 0f steps 1-5: Unique, borrow, reuse, unsafe, unboxed
                │    (only needs 0d — NOT blocked on 0e)
                │
                ├── 0g: GADTs, Eff kind, assoc types, supertraits
                │    (only needs 0d + 0c — NOT blocked on 0f)
                │    │
                │    └── 0h: stdlib, deriving, error messages
                │         │
                │         └── Phase 1: self-hosting
                │
                ├── lean formalization phase 2 (parallel)
                ├── testing: benchmark harness + test runner (parallel)
                └── semantic introspection platform (cross-cutting)

Parallelism after 0d lands:
  0e ──────────┐
  0f steps 1-5 ├── can all run concurrently
  0g ──────────┘
  lean, testing ── parallel tracks throughout

Critical path to "hello world compiles":  0d → 0e (IO handler)
Critical path to self-hosting:            0d → 0g → 0h → Phase 1

Cross-cutting (read before implementing any phase):
  performance-backend-strategy.md  → 0d, 0e, 0f
  testing.md                       → 0d+
  runtime-introspection-mcp.md     → 0b-0d
  lean-formalization.md            → 0c, 0d, 0e (parallel)
  tooling-dx.md                    → 0a through Phase 2
```
