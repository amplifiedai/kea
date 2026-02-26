# Brief: Effects as Platform — Capabilities Kea Unlocks

**Status:** design
**Priority:** Phase 0e-1 (effect surface design), Phase 2-3 (platform features)
**Depends on:** 0c-effect-handlers, 0e-runtime-effects
**Blocks:** agent-native story, plugin ecosystem, portable execution story

## Motivation

A fast, portable, effects-oriented language unlocks opportunities that are
hard to do cleanly in "normal" languages. Effects make cross-cutting behavior
explicit, composable, testable, and optimizable. This brief captures the
platform-level capabilities that Kea's effect system enables — things that
are genuinely new or dramatically easier than in incumbent stacks.

This is not a feature list. It's a design constraint document: these are the
use cases the effect surface must support. Decisions about effect granularity,
handler semantics, and capability boundaries should be evaluated against
these platform goals.

## Core Insight

**Policy violations become type errors, not security reviews.**

If the effect set is the contract, then "no network in this module" is not
a lint rule — it's a compile error. A function with `->` (pure) is
guaranteed deterministic. A function with `-[IO]>` is not. The type system
makes this distinction structural, checkable, and composable.

This is the elevator pitch. Everything below follows from it.

## Platform Capabilities

### 1) Policy-as-code that the compiler enforces

Not lint rules — actual compile-time guarantees:

- No network in this module (function lacks `Net` effect)
- No disk writes in this pipeline (function lacks `IO`)
- This agent can only call these tools (effect set = capability set)
- This function is deterministic (pure, or `Clock`/`Rand` with seeded handlers)

Applications:
- **Agent safety**: agent capabilities are effect signatures, not runtime checks
- **Regulated environments**: compliance is structural, not procedural
- **Multi-tenant plugins**: capability scope is the effect set
- **Production vs simulation**: same code, different handlers

### 2) Deterministic simulation via record/replay

Effects make the practical subset of "time-travel debugging" achievable:

1. **Record**: handler wraps each effect operation, logs args + results
   as structured events
2. **Replay**: handler reads from recorded log instead of performing effects
3. **Step-through**: inspect "what did we read/emit/send?" at each point

Implementation phases:
- Phase 1 (library-level): `RecordingHandler` that wraps any effect handler,
  logs operations as structured `EffectEvent` values. Trivial to implement.
- Phase 2 (library-level): `ReplayHandler` that reads from a recorded log.
  Validates that the replayed code performs the same operations in the same
  order (divergence = bug found).
- Phase 3 (tooling): step-through debugger UI that shows effect timeline.

This is especially valuable for:
- Agentic systems where "why did it do that?" matters more than stack traces
- Flaky test debugging (record a failing run, replay deterministically)
- "Golden run" regression tests for workflows

### 3) Safe plugin ecosystems without capability leaks

Most plugin systems devolve into "here's an object that can do everything"
or "we sandbox at runtime and pray." With effects:

- Plugin can parse, transform, reason (pure, `->`)
- Plugin cannot do IO unless explicitly granted (`-[IO]>`)
- Plugin cannot spawn/communicate unless explicitly granted (`-[Send, Spawn]>`)
- Capability scope is the effect set, enforced at compile time

Applications:
- IDE extensions (parse + transform, no IO)
- Build pipeline steps (read + write specific paths, no network)
- Data transforms (pure computation, no side effects)
- Workflow steps in orchestration engines (scoped tool access)

This is the same model as the typed grammar interface (`Compile` capability
gating for grammars) but generalized to any plugin boundary.

### 4) Ambient context without globals

Effects replace thread-locals and global state for implicit context:

- Tracing spans (`Trace` effect)
- Request IDs, auth context (`Context` effect or parameterized)
- Locale/timezone (`Locale` effect)
- Feature flags (`FeatureFlag` effect)

In most languages you pass context manually or use thread-locals (hard to
test, leak across async boundaries). With effects:

- Define the context effect
- Handler injects the value
- Code reads it without global state
- Tests swap handlers for deterministic context

This is "dependency injection" but structural and compiler-checked.

### 5) Portable execution substrates via effect lowering

Write code once, then:
- Run locally (direct handlers)
- Run in a sandbox (restricted handlers)
- Run distributed (send/route handlers)
- Run on GPU (validate a pure numeric subset and lower)
- Run inside a query engine (UDF lowering)

The effect boundary *is* the portability boundary:
- Pure (`->`) can be offloaded anywhere
- `-[IO]>` must run where IO is available
- `-[Net]>` must run where network is available

The trick is validated sublanguages:
- "GPU subset" is not the whole language — it's `->` functions over
  numeric types that satisfy shape constraints
- "UDF subset" is not the whole language — it's `->` functions over
  serializable types
- Effects + type constraints enforce the boundary at compile time

This connects to the `Compile` effect and comptime infrastructure:
validated subsets can be checked and lowered by comptime extensions.

### 6) Structurally derived observability

Instead of "sprinkle logs," define effect surfaces:

- `Log` effect → structured log events
- `Metric` effect → counters, histograms, gauges
- `Trace` effect → spans with context propagation

Then:
- Production handler routes to OpenTelemetry
- Test handler captures structured events for assertion
- Agent queries summaries via Introspect surface

You get "observability by default" without forcing everyone to buy into
one library API. The effect contract is the interface; the handler is
the backend.

### 7) Agent-native APIs

Effects can represent:
- Tool calls (`Tool.search(query)`, `Tool.execute(code)`)
- Model inference (`Think.complete(prompt)`)
- Memory reads/writes (`Memory.recall(key)`, `Memory.store(key, value)`)
- External actions (`Action.send_email(...)`, `Action.create_ticket(...)`)

This means:
- Agent capability set = effect signature
- Policy changes = type errors (add/remove effects)
- Runtime can simulate or audit everything (via record/replay handlers)
- Agents can introspect their own capabilities (effect reflection)

This is a genuine new platform play. Most agent stacks are glued together
with dynamic JSON and best-effort validation. Kea can make agent policies
structural and compiler-checked.

### 8) Effects as memory optimization proofs

The deepest platform unlock may be memory performance. Effects
structurally prove properties about memory that other languages
discover heuristically — or can't discover at all.

**The core insight:** Rust requires explicit lifetime annotations to
prove memory safety. Kea gets equivalent (and sometimes stronger)
information from effect signatures that programmers are already
declaring for functionality reasons. The memory optimization is a
_free rider_ on the effect system.

What effects prove about memory:

| Effect signature | What it proves | Memory optimization |
|-----------------|----------------|---------------------|
| `->` (pure) | No storage, no aliasing, no escape except return | Skip retain/release on arguments, stack-allocate intermediates |
| `-[Fail E]>` only | Same as pure (early return, not storage) | All pure optimizations apply |
| No `Send`/`Spawn` in scope | Value is thread-local | Non-atomic refcounts |
| `handle` block (tail-resumptive) | Known lifetime scope, no continuation capture | Region/arena allocation, bulk deallocation |
| `Alloc` handler scope | Explicit arena lifetime | Bump allocation + no individual frees |
| `Unique T` + pure scope | Provably RC==1 for all intermediates | Skip runtime RC checks on functional update chains |

**Why this matters for the platform story:** every effect signature
a programmer writes for correctness, policy, or testability also
gives the compiler memory optimization information for free. The
same `->` that means "this function is deterministic" also means
"this function can't alias its arguments." The same `handle` block
that means "errors are caught here" also means "these allocations
die here."

This is not an optimization pass bolted on after the fact — it's a
structural consequence of the effect system's design. The normative
optimization contracts are in the [memory model brief](../todo/0f-memory-model.md)
(§ Type-System-Driven Memory Optimizations).

## Effect Surface Design Requirements

These platform capabilities impose design constraints on which effects
are standardized and how they're granularized.

### Critical: IO must be decomposed

If `IO` is a monolithic effect (file + network + clock + random + stdout),
you lose the ability to express fine-grained policies. The following must
be **separate** capability effects:

| Effect | Scope | Why separate |
|--------|-------|-------------|
| `IO` | File read/write, stdout/stderr | Core system IO |
| `Net` | Network connections, HTTP, DNS | Policy: "no network in this module" |
| `Clock` | System time, monotonic clock | Deterministic simulation: seed time |
| `Rand` | Random number generation | Deterministic testing: seed RNG |
| `Log` | Structured log emission | Observability without IO |
| `Trace` | Span creation, context propagation | Observability without IO |

`Clock` and `Rand` being separate from `IO` is the critical decision.
If they're lumped together, you can't say "this function can read the
clock but can't do network" — and that granularity is what makes
policy-as-code (#1) and deterministic simulation (#2) work.

### Standardize early (0e-0h timeframe)

These effect surfaces should be defined and stable before Phase 1:

**Already planned:**
- `IO` — 0e, file/stdout
- `Fail E` — 0c, error handling
- `Send` / `Spawn` — 0e, actor model
- `Log` — mentioned in 0e
- `State S` — mentioned in 0e (library effect)
- `Alloc` — 0e/0f, arena allocation

**Add to 0e/0h scope:**
- `Clock` — system time, monotonic time. Handler can inject fixed/simulated time.
- `Rand` — random number generation. Handler can inject seeded RNG.
- `Net` — network connections. Separate from file IO for policy granularity.
- `Trace` — span creation, context propagation. Structured tracing.

### Standardize later (Phase 2+)

- `Metric` — counter/histogram/gauge emission
- `Introspect` — runtime self-query (see runtime-introspection-mcp.md)
- Tool/Agent effects — domain-specific, library-level
- GPU/UDF lowering contracts — requires validated sublanguage infrastructure

## Relationship to Existing Briefs

| Brief | Relationship |
|-------|-------------|
| [0e-runtime-effects](../todo/0e-runtime-effects.md) | IO decomposition (IO vs Net vs Clock vs Rand) affects 0e's standard effect set |
| [testing](../todo/testing.md) | Record/replay (#2) extends the testing model. `Clock`/`Rand` separation enables deterministic tests. |
| [runtime-introspection-mcp](runtime-introspection-mcp.md) | Observability (#6) and agent introspection (#7) feed into the introspection platform |
| [packaging-ffi-comptime](packaging-ffi-comptime.md) | Safe plugins (#3) extend the effect-based permissions model |
| [typed-grammar-interface](typed-grammar-interface.md) | Grammar `Compile` capability is an instance of #3 (safe plugins) |
| [0f-memory-model](../todo/0f-memory-model.md) | Effects as memory proofs (#8) — pure retain elision, handler-scoped regions, effect-directed atomicity |
| [performance-backend-strategy](performance-backend-strategy.md) | Optimization requires trustworthy effect classification |
| [lean-formalization](../todo/lean-formalization.md) | Policy-as-code (#1) properties are provable: "pure function has no IO" is a theorem |

## Top 3 Platform Unlocks

If Kea is fast + portable + effects-native, the highest-value plays are:

1. **Policy-checked agent orchestration** — safe tools, sandboxing,
   auditability. Agent capabilities are type-checked effect signatures.
2. **Deterministic simulation/testing** — record/replay via handler
   swapping. Eliminate flaky tests, enable "golden run" regression.
3. **Validated lowering to other substrates** — UDFs, WASM, GPU kernels.
   Effect boundary = portability boundary, enforced at compile time.

These are both compelling and hard to replicate in incumbent stacks.

## Non-Goals (this brief)

- Detailed API design for each effect (that's 0e/0h/library work)
- GPU compiler or query engine integration (Phase 3+)
- Agent framework design (library-level, post-Phase 1)
- Specific observability vendor integrations (library-level)

## Open Questions

- Should `IO` be decomposed into `FileIO` + `StdIO` or kept as one?
  (Proposal: keep as one for v1. File and stdout are usually co-granted.
  The important split is IO vs Net vs Clock vs Rand.)
- Should `Clock` and `Rand` be capability effects (direct runtime call)
  or regular effects (handler-dispatch)? (Proposal: capability effects
  with test-interceptability, same as IO/Send/Spawn per 0e decisions.)
- How fine-grained should `Net` be? (`Net` vs `Http` + `Dns` + `Tcp`?)
  (Proposal: single `Net` for v1. Decompose later if there's demand.)
