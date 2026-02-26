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
