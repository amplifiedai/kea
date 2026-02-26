# Brief: Tooling and Developer Experience

**Status:** design
**Priority:** Phase 0 (parallel track) through Phase 2
**Depends on:** 0a-lexer-parser (formatter), 0b-type-system-core (LSP, MCP), 0d-codegen-pure (test runner, build)
**Blocks:** public release, package ecosystem

## Motivation

Kea's type system is the competitive advantage. But a type system
without world-class tooling is an academic exercise. The DX must
be at the Rust/Elixir level — and in specific areas it must exceed
them, because the effect system enables things no other language's
tooling can do.

Go pioneered the blessed-tooling model: `go fmt`, `go test`,
`go build`, `go vet`, `go doc` — all in one binary, all
non-negotiable. Deno pushed further: formatter, linter, test
runner, bundler, permissions. Elixir's mix is beloved because it
ships enough that you rarely need third-party build tools.

Kea goes further than all of these because the effect system gives
tooling information that other languages don't have.

## The `kea` Binary

Everything ships in one binary. No external tools required for
the core workflow.

| Command | What | Phase |
|---------|------|-------|
| `kea run <file>` | Execute a Kea program | 0d |
| `kea build` | AOT compile via Cranelift | 0d |
| `kea check` | Type-check only (no codegen) | 0b |
| `kea test` | Built-in test runner | 0d |
| `kea fmt` | Formatter (zero config) | 0 parallel |
| `kea repl` | Interactive shell | 0d |
| `kea doc` | Documentation generator | 0h |
| `kea pkg` | Package management | Phase 2 |
| `kea lsp` | Language server | 0 parallel |
| `kea mcp` | MCP server for agents | 0b |
| `kea init` | Project scaffolding | 0d |

### The Formatter is Non-Negotiable

For an indentation-sensitive language, the formatter is not a
convenience — it's a correctness tool. If two developers indent
differently, their code has different semantics. `kea fmt` must:

- Be zero-config. One style. No options. No `.keafmt.toml`.
- Be idempotent. `kea fmt | kea fmt` = `kea fmt`.
- Preserve comments and blank lines.
- Handle the hard cases: long effect annotations, deeply nested
  pattern matches, multi-line function signatures.
- Run on save in every editor (via LSP formatting).

Go's `gofmt` ended formatting wars. Kea's `kea fmt` must do the
same, and for Kea it's even more critical because indentation is
semantic.

Cannibalises rill-fmt's doc algebra (~146 LOC) and comment
infrastructure (~131 LOC). Printer and all format rules need
rewriting for indent-sensitive output.

### The Test Runner

See **[testing brief](testing.md)** for the full design. Summary:

- **`assert` (Fail) + `check` (Test effect):** two assertion modes.
  `assert` stops the test (precondition). `check` accumulates
  failures and continues (observation). The handler decides
  accumulation semantics, not the call site.
- **Expression capture:** the compiler rewrites assertions in test
  blocks to capture sub-expression values. Structural diff for
  records via row types.
- **Effect-driven parallelism:** pure + Fail-only tests parallel
  by default. IO/concurrency tests sequenced, opt-in parallel.
- **Property testing:** `Gen` effect, `@derive(Arbitrary)`,
  seed replay via `--replay`.
- **Structured results:** `TestResult` type rendered by CLI or
  consumed as JSON by MCP/CI.

## What Only Kea Can Do

### Effect-Aware Documentation

`kea doc` shows not just types but effects. For every function:

```
fn load_config(_ path: String) -[IO, Fail ConfigError]> Config
  ^^^^^^^^^^^^^^^^^^^^^^^^^^   ^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^
  what goes in                 what it does              what comes out
```

The documentation shows the full contract. No other language's
doc tool can do this because no other language tracks effects.
Users see at a glance: "this function reads the filesystem and
can fail."

### Effect-Aware Package Registry

A package's effect surface is visible in the registry:

- **Pure packages** (`->`): provably can't do IO. Can't phone
  home, can't read your filesystem, can't exfiltrate data.
  Compile-time enforced, not a trust model.
- **IO packages** (`-[IO]>`): touch the outside world. Visible
  in the registry. Users know what they're opting into.
- **Send/Spawn packages**: use concurrency. Visible.

This is a genuine security innovation. No existing registry
can tell you whether a package is pure. Kea's can, because the
compiler proves it.

### Effect-Aware Test Isolation

See [testing brief](testing.md) for details. Handler-based mocking
replaces mock frameworks entirely — swap the handler, not the code.
The compiler verifies handler/effect signature match.

### Structured Diagnostics for Agents

Already designed (see PEDAGOGY.md "Errors as first-class
citizens"). The MCP server returns machine-readable `Diagnostic`
JSON. Agents can programmatically navigate errors, pattern-match
on stable error codes, and apply fixes. The same `Diagnostic`
type renders via ariadne for human CLI output.

### Effect-Driven Static Analysis

This is Kea's deepest tooling advantage. Most static analysis in other
languages tries to RECOVER information the type system discarded (alias
sets, side effects, data flow, capability boundaries). Kea's effect
system KEEPS that information structurally. Analyses that require
whole-program interprocedural fixpoint computation in C/Java/Rust
become local signature reads in Kea.

Every analysis below is available to both humans (LSP) and agents (MCP).

#### Automatic parallelisation detection

The effect row proves independence. A tool scans consecutive let bindings,
reads their effect signatures, checks data dependencies, and identifies
parallelisable groups:

```kea
-- before: sequential
let users = load_users(ids)       -- -[IO]>
let config = parse_config(raw)    -- ->
let schema = validate(spec)       -- -[Fail E]>

-- LSP code action: "Run 3 independent bindings in parallel"
let (users, config, schema) = Par.all3(
  || -> load_users(ids),
  || -> parse_config(raw),
  || -> validate(spec)
)
```

Not a heuristic. The effect system PROVES there are no data dependencies,
no shared mutation, no ordering requirements. The transformation is
correct by construction.

The inverse is equally valuable: if someone writes `Par.all3` on calls
that share `State S`, the tool flags "these share mutable state —
parallel execution is unsound." Before compile. Before ship.

**LSP:** code action on sequential bindings.
**MCP:** `find_parallelisable_blocks` tool returns parallelisation
opportunities with proof (effect signatures that demonstrate independence).

#### Capability boundary enforcement

The effect row IS a capability set. Architectural constraints become types:

```kea
-- type aliases as architectural boundaries
type BusinessLogic T = () -[Fail DomainError, Log]> T
type DataLayer T = () -[Fail DbError, State Connection]> T
type HttpHandler T = () -[IO, Net, Fail HttpError]> T
```

A function claiming to be BusinessLogic that sneaks in an IO call won't
compile. This is not a linter rule — it's the type system.

**LSP:** hover shows which architectural layer a function lives in based
on its effect signature. Warnings when a function exceeds its layer's
allowed effects.
**MCP:** `check_capability_boundaries` tool verifies a module's functions
stay within declared effect budgets. Agents can enforce architectural
constraints across a codebase without reading implementations.

#### Dead code elimination and dead effect detection

Pure functions (`->`) with unused return values can be entirely eliminated
— not just the assignment, the call and all its internal allocations. In
C++ you need whole-program alias analysis. In Kea, `->` proves it.

Also: handlers that cover effects the body doesn't perform. The type
system already detects this ("effect handled but not performed"). Tools
can surface this as "unnecessary handler — dead code."

**LSP:** dim/strikethrough unreachable code after `Fail.fail`, unused
pure calls, unnecessary handlers.
**MCP:** `find_dead_code` tool returns provably dead code with effect-based
justification.

#### Security and information flow

A function that reads secret data but has no `IO`, `Net`, or `Send` in
its effect row PROVABLY CANNOT LEAK IT. Information flow control verified
by the type checker. No taint analysis, no interprocedural tracking.

```kea
fn process_secret(data: Secret) -> Summary
  -- pure: cannot exfiltrate. Proven by ->
  summarise(data)

fn process_dangerous(data: Secret) -[Net]> Summary
  -- LSP warning: function has Net access and handles Secret data
  -- MCP: flagged by audit_information_flow
```

**LSP:** warning annotations on functions that combine sensitive types
with exfiltration-capable effects (`IO`, `Net`, `Send`).
**MCP:** `audit_information_flow` tool identifies functions where sensitive
data is in scope AND exfiltration effects are available. Returns the
minimal capability set each function has over each data type.

#### Test coverage by capability

Compute which effects your test suite exercises:

- If no test provides a handler for `Net`, network code has zero
  integration coverage.
- If every test handles `IO` with mocks, filesystem paths are all
  tested in isolation.
- If `State` handlers always start from `State.empty()`, no test
  covers stateful recovery scenarios.

Effect-level coverage is a metric no other language can compute.

**LSP:** gutter annotations showing which effects are tested per function.
**MCP:** `effect_coverage_report` tool returns per-module and per-function
effect coverage matrix. Agents can identify undertested capabilities.

#### Performance classification

The effect row IS the cost model:

| Effect signature | Performance class | Implications |
|-----------------|------------------|--------------|
| `->` | CPU-bound, no alloc pressure | Safe to inline, memoise, parallelise |
| `-[Fail E]>` | CPU-bound + branch | Same as pure for scheduling |
| `-[State S]>` | Mutable state, scoped | No contention, but sequential |
| `-[IO]>` | May block, may syscall | Schedule on IO thread pool |
| `-[Net]>` | Network-bound | May have high latency |
| `-[Send]>` | Crosses threads | Needs atomic refcounting |

A profiler annotates hotspots with their effect classification and tells
you whether the bottleneck is compute, IO, or contention — before you
instrument anything.

**LSP:** effect-derived performance hints on hot paths.
**MCP:** `classify_performance` tool returns performance class for every
function, enabling agents to reason about optimisation strategies without
profiling.

#### Alias analysis (for compiler optimisations)

Unique types give definitive single-ownership. Pure functions can't alias
through side effects. Handler scope boundaries define lifetime regions.

The three hardest problems in alias analysis:
- "Can this pointer escape?" — `->` means no. `borrow` means no.
- "Can this mutation be observed?" — Unique means single owner.
- "Is this value shared?" — effect row tells you (no Send = no sharing).

All have structural answers from the type/effect system instead of
heuristic approximations.

**MCP:** `query_aliasing` tool returns provable aliasing properties for
a binding — useful for agents doing performance optimisation.

#### Architecture visualisation

Render the effect-derived dependency graph for a module. Functions are
nodes. Edges are data dependencies. Effect colours show capability layers.
Parallel groups are visually separated. The entire module's concurrency
and capability structure is visible at a glance.

**LSP:** command to render module effect graph.
**MCP:** `module_effect_graph` tool returns the graph as structured data
for agents to reason about architecture.

#### Refactoring safety

"Extract this block into a function" — the tool computes the extracted
function's effect signature automatically from the types of the
expressions being extracted. No guessing about what to thread through.
The effect row of the extracted function is determined, not chosen.

"Inline this function" — the tool knows whether inlining changes the
effect surface of the call site. If the inlined function is pure, it's
always safe. If it has effects, the tool verifies the call site's
handler coverage still holds.

**LSP:** extract-function code action auto-computes the effect signature.
Inline-function action warns if it changes the enclosing function's
effect row.
**MCP:** `extract_function` and `inline_function` tools return the
refactored code WITH the proven-correct effect signature, so agents
can refactor with type-system-level confidence.

#### Effect budget tracking (CI)

Track the effect surface of your public API over time. Effects are part
of the API contract — if a function gains `Net` where it was pure before,
that's a breaking change.

```
CI: effect surface diff for v1.2.0 → v1.3.0

  BREAKING: Config.parse gained [IO] (was pure)
  BREAKING: Auth.validate gained [Net] (was [Fail AuthError])
  compatible: Pipeline.run added [Log] (additive, not breaking)
```

Additive effects (gaining `Log` alongside existing `IO`) are compatible.
Losing purity or gaining capability effects (`IO`, `Net`, `Send`) is
breaking. The CI tool knows the difference structurally.

**LSP:** warning when a public function's effect signature changes in a
way that breaks callers.
**MCP:** `diff_effect_surface` tool compares two versions of a module
and classifies each change as breaking/compatible/additive. Agents can
gate PRs on effect surface stability.

#### Agent-driven architecture migration

An agent reads the effect graph for a codebase, identifies functions that
should be pure but aren't, and proposes refactorings to push effects to
the boundary:

```
Agent analysis: src/orders.kea

  process_order: -[IO, Log, Fail OrderError]>
    └ validate_order: -[IO]>        ← WHY does validation need IO?
      └ line 42: IO.read_file("rules.json")  ← config loading in validation

  Recommendation: extract config loading to caller, make validate_order pure.
  Confidence: proven safe (no other IO operations in validate_order body).
```

The agent doesn't guess that the refactoring is safe. It reads the effect
row, identifies the single IO operation, and proves that extracting it
makes the function pure. The type system verifies the result.

**MCP:** `suggest_purity_refactorings` tool identifies functions that
are "almost pure" (one or two effect operations that could be moved to
the caller) and returns the refactoring with a proof of correctness.

#### Supply chain auditing

A dependency's effect surface IS its trust boundary. Audit package
updates by diffing effect surfaces:

```
Package update: http-client 2.0.0 → 3.0.0

  NEW capability: Rand (used in request ID generation)
  NEW capability: Clock (used in retry backoff)
  REMOVED capability: Spawn (connection pool now sync)
  UNCHANGED: Net, IO, Fail

  Risk assessment: Rand+Clock are low-risk additions.
  Spawn removal reduces concurrency surface.
```

No source code review needed for capability assessment. The effect
signatures are the complete capability manifest.

**MCP:** `audit_dependency_effects` tool diffs effect surfaces between
package versions and flags capability escalation. Agents can
automatically approve low-risk updates and flag high-risk ones.

#### Deterministic simulation and replay

Functions whose effects are fully handled can be deterministically
replayed. Record the handler responses (IO reads, network responses,
random values, timestamps) and replay them. The effect system guarantees
that the replay is faithful — same inputs to handlers, same program
behavior.

```kea
-- record mode: wrap production handlers with recording
let trace = record_effects
  handle app.run()
    IO.read_file(p) -> ...    -- record: (read_file, "config.toml") → "..."
    Net.get(url) -> ...       -- record: (get, "https://...") → response
    Clock.now() -> ...        -- record: (now) → 1709123456

-- replay mode: use recorded responses as handler
replay_effects(trace)
  handle app.run()
    IO.read_file(p) -> resume(trace.next_response())
    Net.get(url) -> resume(trace.next_response())
    Clock.now() -> resume(trace.next_response())
```

This is deterministic simulation for free. Every effectful program is
implicitly record/replayable because effects separate what happens from
how it happens.

**MCP:** `generate_replay_harness` tool creates a replay handler from
a recorded trace. Agents can reproduce production bugs deterministically
without accessing production systems.

#### Effect-aware code search

"Find all functions that can access the network" is a type query, not
a grep. "Find all pure functions that take a String" is a type query.
"Find all functions that handle IO but don't perform Net" is a type query.

```
> kea query "fn(_ : String) -[Net]> _"
  src/http.kea:42   fetch(url: String) -[Net, Fail HttpError]> Response
  src/dns.kea:15    resolve(host: String) -[Net]> IpAddr
  src/ws.kea:8      connect(url: String) -[Net, IO]> Socket
```

Effect-aware search is structural, not textual. It finds functions by
what they DO, not what they're named or where they live.

**LSP:** workspace symbol search with effect filters.
**MCP:** `query_by_effects` tool returns functions matching an effect
pattern. Agents can find relevant code by capability, not by guessing
file names.

#### Automatic memoisation

A pure function (`->`) is referentially transparent. A tool can
automatically wrap it with a cache — and more importantly, it can
tell you exactly why memoisation is UNSAFE for effectful functions:
"can't memoise `load_config` because it performs IO (result may differ
between calls)."

For `-[Fail E]>` functions, memoisation of the success path is still
valid (fail is deterministic for a given input). The tool can offer
conditional memoisation: cache `Ok` results, re-execute on `Err`.

**LSP:** code action "Memoise this pure function" on `->` functions.
Warning on effectful functions explaining why not.
**MCP:** `suggest_memoisation` tool identifies hot pure functions in a
call graph and proposes caching with zero false positives.

#### Incremental computation

If you know which functions are pure and which inputs changed, you know
exactly what to recompute. This is build-system-level incrementality
applied to arbitrary computation.

For the compiler itself this is wild: the compilation pipeline is a chain
of typed, effect-annotated functions. When a source file changes, the
effect/type system tells you which downstream passes are invalidated and
which cached results are still valid. Incremental recompilation falls out
of the same analysis that works for user programs.

More generally: any pure function that hasn't had its inputs change
doesn't need re-execution. The effect system tells you which functions
are pure. A reactive runtime (or build system, or CI pipeline) uses this
to compute the minimal re-execution set.

**LSP:** incremental type-checking already benefits (pure helper functions
don't need rechecking when unrelated code changes).
**MCP:** `minimal_recomputation_set` tool returns exactly which functions
need re-execution given a set of changed inputs. Agents can build
incremental pipelines with compiler-proven correctness.

#### Formal verification targeting

Pure functions are the easiest to formally verify. A tool can rank
functions by "verification difficulty" based on their effect rows:

| Effect signature | Verification difficulty | Why |
|-----------------|------------------------|-----|
| `->` | Low | Referentially transparent, no state |
| `-[Fail E]>` | Low | Equivalent to Result, total with catch |
| `-[State S]>` | Medium | Stateful but scoped, handler bounds it |
| `-[IO]>` | High | External world, non-deterministic |
| `-[Send, Spawn]>` | Very high | Concurrent, interleaving |

Agents doing formal verification can automatically prioritise the
low-hanging fruit and build verification coverage bottom-up from the
pure core outward.

**MCP:** `rank_verification_targets` tool returns functions sorted by
verification tractability, with the effect-based justification.

#### Effect-based cloud cost estimation

The effect row approximates the cost model for serverless/cloud:

- `-[Net]>` → network egress costs
- `-[IO]>` → disk IOPS
- `-[Clock]>` → timer/scheduler costs
- `->` → pure compute only

A tool can estimate relative cost profiles per function without runtime
instrumentation. "This Lambda's signature is `-[Net, IO, Clock]>` —
expect network, disk, and timer costs." Useful for capacity planning
and cost allocation.

**MCP:** `estimate_cost_profile` tool returns per-function cost
classification based on effect signatures.

#### Effect-aware debugger

This deserves deep treatment — see dedicated section below.

### The Debugger

Kea's effect system gives the debugger information that no other
debugger has: the complete capability context at every point in
execution. This isn't about adding effect awareness to a traditional
debugger. It's about building a fundamentally different kind of
debugger where effects are the primary navigation primitive.

#### Effect context at every frame

When you hit a breakpoint, the debugger knows:

- **Which handlers are installed.** "You're inside a `with_mock_fs`
  handler — `IO.read_file` will return mock data, not real files."
- **The full effect stack.** Which handlers are nested, in what order,
  what each one intercepts.
- **What the current function CAN do.** The effect row is the
  capability set. If the function is `->`, you know there are no side
  effects anywhere in this frame. If it's `-[State Int]>`, you know
  there's mutable state but it's scoped to this handler.
- **What it CANNOT do.** Equally important. If `Net` isn't in the
  effect row, this function provably can't touch the network. No need
  to worry about network-related bugs here.

This is the debugger equivalent of Kea's type signatures: you can
look at a stack frame and know what it does, not just where it is.

```
Breakpoint at src/orders.kea:42  process_order()

  Effects: [Log, State Stats, Fail OrderError]
  Handlers:
    Log       → with_stdout_logger (src/main.kea:15)
    State     → with_stats (src/main.kea:14)  current: Stats { count: 7 }
    Fail      → catch (src/main.kea:18)

  This function CANNOT: IO, Net, Send, Spawn, Rand, Clock
  This function CAN: log messages, read/write Stats, fail with OrderError
```

#### Handler-aware stepping

Traditional debuggers step through call stacks. Kea's debugger steps
through effect operations and their handlers:

- **Step into effect:** when execution hits `Log.log(Info, msg)`,
  "step into" takes you to the handler clause that intercepts it
  (e.g., `with_stdout_logger`'s Log handler), not into the `Log`
  module (which has no implementation — effects are abstract).
- **Step to resume:** from inside a handler body, "step to resume"
  jumps to where control returns to the handled code after `resume`.
- **Step over handler:** when an effect is performed, "step over"
  executes the handler body and resumes in one step, showing you
  the resume value without entering the handler.
- **Break on effect:** "break when `IO.read_file` is performed"
  triggers regardless of where in the code the call happens. Effect
  breakpoints are structural, not location-based.

This means you can debug at the ARCHITECTURE level. "Break on any
network access" is `break Net.*`. "Break on any state mutation" is
`break State.put`. "Break on any error" is `break Fail.fail`. You're
debugging capabilities, not code locations.

#### Handler scope visualisation

The debugger can render the handler stack as a visual scope tree:

```
main()
 └─ handle IO (runtime)
     └─ handle Log (with_stdout_logger)
         └─ handle State Stats (with_stats, current: { count: 7 })
             └─ handle Fail OrderError (catch)
                 └─ process_order()        ← YOU ARE HERE
                     └─ validate_order()   ← stepping into
```

Each handler frame shows:
- Which effect it handles
- The handler's current state (for stateful handlers like State)
- Whether the handler is tail-resumptive (inlined — no actual frame)
  or non-tail (real continuation capture)

#### Low-level debugging for systems work

For Kea to be systems-adjacent and a compiler-writing language, the
debugger needs to go deep. This is where the COMPILER-AS-DATA vision
and Grammar blocks make things interesting.

**Memory layout inspection:**
```
(kea-debug) inspect value orders
  Type: List(Order)
  Representation: Cons cell (refcount: 1, UNIQUE — safe to mutate)
  Layout: [tag: u8 | ptr: *Cons { head: Order, tail: List(Order) }]
  Head:
    Order { id: 42, total: 199.99 }
    Layout: [field 0 (id): i64 @ offset 0 | field 1 (total): f64 @ offset 8]
    Size: 16 bytes, align: 8
  Refcount: 1 (non-atomic, no Send in scope)
```

The debugger knows the memory layout because the compiler computed it.
It knows the refcount atomicity because the effect row determined it.
It knows uniqueness because the type system tracks it. This is
information that C/C++ debuggers guess at via DWARF metadata — Kea's
debugger knows structurally.

**Ptr and @unsafe debugging:**
```
(kea-debug) inspect ptr buf.data
  Ptr(UInt8) @ 0x7fff4a002000
  Backing: malloc (foreign allocation, not refcounted)
  Unsafe context: yes (inside @unsafe fn Buffer.push)
  WARNING: Ptr into non-managed memory — debugger cannot track liveness
```

For @unsafe code, the debugger surfaces what it can prove (allocation
source, unsafe context) and explicitly flags what it can't (liveness
of raw pointers). Honest about its limits.

**Cranelift IR correlation:**
When debugging compiler internals (or any Grammar-based language
implementation), the debugger can show the correspondence between
Kea source, HIR, MIR, and Cranelift IR:

```
(kea-debug) show-ir
  Source:  let x = a + b
  HIR:     HirExpr::BinaryOp { op: Add, left: HirExpr::Var("a"), right: HirExpr::Var("b") }
  MIR:     %3 = binary add %1, %2
  CLIF:    v3 = iadd v1, v2
```

This is the debugger for compiler writers. When a Grammar block
lowers a DSL to MIR, you can see each layer of the translation. When
an optimization pass transforms MIR, you can see before/after with
the pass name and its effect signature (which tells you what kind
of transformation it is).

**Reuse analysis debugging:**
```
(kea-debug) inspect reuse xs
  List(Int), refcount: 1
  Reuse analysis: ELIGIBLE (refcount proven == 1, Perceus drop-before-last-use)
  Next mutation: xs.map(|x| -> x + 1)
    → will execute IN-PLACE (no allocation)

(kea-debug) inspect reuse shared_xs
  List(Int), refcount: 3
  Reuse analysis: NOT ELIGIBLE (refcount > 1)
  Next mutation: shared_xs.map(|x| -> x + 1)
    → will COPY (new allocation, 24 bytes)
```

The programmer can see exactly when reuse analysis fires and when it
doesn't. This is the "why is my program allocating?" debugger — and
it's not a profiler heuristic, it's the compiler telling you its
actual decision and why.

**Effect handler compilation inspection:**
```
(kea-debug) show-handler State
  Handler: with_stats (src/main.kea:14)
  Classification: tail-resumptive
  Compilation: INLINED (no evidence struct, no indirect call)
  State.get() → read local var `stats` @ rbp-16
  State.put(s) → write local var `stats` @ rbp-16
  Overhead vs parameter-passing: 0% (identical codegen)
```

For performance-sensitive code, the debugger shows HOW effects are
compiled. Is this handler inlined or going through evidence dispatch?
Is the evidence struct heap-allocated or stack-allocated? What's the
actual machine code for an effect operation? This answers "are effects
zero-cost here?" with concrete evidence.

#### DAP integration

The debugger exposes all of the above through the Debug Adapter
Protocol (DAP) so it works in VS Code, Neovim, and any DAP client.
Custom DAP extensions for Kea-specific features:

- Effect context in stack frame metadata
- Handler-aware step commands
- Effect breakpoints
- Memory layout inspection
- IR correlation views

#### MCP debugger interface

Agents get the same debugger capabilities through MCP:

- `debug_effect_context` — handler stack and capability set at a point
- `debug_break_on_effect` — set effect-based breakpoints
- `debug_inspect_layout` — memory layout for a value
- `debug_show_ir` — multi-level IR correlation
- `debug_reuse_analysis` — allocation decisions for a value
- `debug_handler_compilation` — how an effect handler was compiled

An agent debugging a performance issue can: query the effect context,
check handler compilation classification, inspect reuse analysis
decisions, and identify whether the bottleneck is handler dispatch,
allocation, or pure computation — all through structured MCP tools
without reading source code heuristically.

#### The meta-insight

Every analysis above is LOCAL. Read the function signature, know the
answer. No whole-program analysis, no call graphs, no fixpoint iteration.
The effect row is a pre-computed summary of everything expensive analyses
try to discover. And it's maintained incrementally by the type checker —
every edit updates it.

This is why the MCP story is as strong as the LSP story. Agents don't
need to "understand" code heuristically. They read the types. The effect
signatures are machine-readable analysis summaries that the compiler
maintains and guarantees.

All analyses consume the same semantic platform defined in the
[semantic introspection brief](runtime-introspection-mcp.md). One
engine, many consumers. The introspection brief defines the platform
contract. This section defines what's built on top of it.

## Decisions

- **Zero-config formatter.** No options. One style. This is
  even more important than Go's gofmt because indentation is
  semantic in Kea.

- **Tests are language syntax, not a framework.** `test` blocks
  are first-class. The compiler knows about them. No test
  framework dependency.

- **Everything in one binary.** No `cargo install` equivalent
  for core tools. The formatter, test runner, LSP, MCP server,
  REPL, and package manager all ship in `kea`.

- **Effect signatures in documentation.** The full effect
  annotation appears in generated docs. This is the feature
  that makes Kea's docs qualitatively better than any other
  language's.

- **No plugin API for tooling.** The formatter, linter, and
  test runner are not extensible via plugins. They're opinionated
  and blessed. Third-party tools can use the compiler as a
  library (same APIs the MCP server uses) but can't modify the
  blessed tools.

## Implementation Timeline

### Phase 0 parallel track (weeks 2-6)
- Tree-sitter grammar (standalone, no compiler dependency)
- Formatter (`kea fmt`) — cannibalise rill-fmt
- Basic LSP (hover, go-to-def, diagnostics)
- Neovim plugin (tree-sitter + LSP)

### Phase 0b-0d
- MCP server (immediately after type checker works)
- `kea check` (type-check only)
- `kea run` / `kea build` (after codegen)
- `kea test` (after codegen)
- `kea repl` (after evaluator or codegen)

### Phase 2
- `kea doc` (after stdlib and @derive stabilise)
- `kea pkg` (package management — see packaging brief)
- `kea init` (project scaffolding)

## Open Questions

- Should `kea lint` be separate from `kea check`? Go has
  `go vet` separate from compilation. Rust has clippy separate
  from rustc. Kea could fold lint rules into `kea check` since
  effects already catch many things linters check for (unused
  IO, unreachable code after fail, etc.).

- Should the REPL support effect visualisation? (Show which
  effects each expression performs, highlight pure vs effectful
  code.) This would be a unique REPL feature.

- How should `kea test` handle benchmarks? Built-in benchmarking
  (like Go's `testing.B`) or separate tool?
