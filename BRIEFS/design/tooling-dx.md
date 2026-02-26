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
