# Kea Programming Language

Kea is a statically-typed functional programming language with algebraic effects, handlers, row polymorphism, and indentation-sensitive syntax. It compiles via Cranelift. The bootstrap compiler is implemented in Rust, cannibalising infrastructure from the [Rill](https://github.com/cigrainger/rill) project.

**Read `docs/INDEX.md` for the complete documentation suite.** Key references: `docs/spec/KERNEL.md` (kernel specification), `docs/spec/CALL-SYNTAX.md` (method dispatch), `docs/spec/ROADMAP.md` (implementation plan). This document covers how to work on the codebase.

---

## Philosophy

**This project operates at agentic-era pace.** The entire Rill codebase — 16 Rust crates, full HM type inference with Rémy row unification, Cranelift codegen, MCP server, LSP, formatter, tree-walking evaluator, Lean proofs, 2000+ tests — was written from scratch in 17 days (1,088 commits, Feb 9–26 2026). Not adapted. Not forked. Written.

Kea cannibalises that infrastructure. Most of the hard work — the unifier, the row solver, the codegen pipeline, the diagnostic system — already exists in battle-tested form. Kea's job is to extend it with effects, handlers, and indentation-sensitive syntax. This is not a multi-month project. Phase 0 (lexer through codegen) can land in days, not weeks.

**Do not create artificial phase boundaries.** If the work is ready and the dependencies are met, do it now. Don't defer to a later phase what can land today. Don't split a coherent feature into multiple PRs for the sake of "smaller changes." Ship the correct design, not a stopgap you know you'll rewrite.

**Be aggressive about completion.** When you finish a step, immediately start the next one. When you finish a brief, move it to `done/` and pick up the next unblocked brief. The bottleneck is never "is this ready" — it's "are we moving fast enough." Check the dependency graph in INDEX.md and always be working on the critical path.

---

## Crate Map

This is the **target architecture**. Crates will be created as their respective phases begin.

| Crate | Purpose | Key Types | Cannibalises |
|-------|---------|-----------|--------------|
| `kea` | CLI entry point | `main()` | `rill` |
| `kea-syntax` | Lexer + indentation-sensitive parser | `Lexer`, `Parser`, `Token`, `Layout` | `rill-syntax` (rewrite for indent) |
| `kea-ast` | AST node definitions, source spans | `Expr`, `Decl`, `Pattern`, `Span` | `rill-ast` |
| `kea-types` | Type representations | `Type`, `RowType`, `Effect`, `Handler` | `rill-types` (extend for effects) |
| `kea-infer` | HM type inference, Rémy-style unification, effect inference | `InferCtx`, `Unifier`, `Substitution` | `rill-infer` (extend for effects) |
| `kea-hir` | High-level IR (desugared, name-resolved, typed) | `HirExpr`, `HirDecl` | new |
| `kea-mir` | Mid-level IR, optimisation passes | `MirExpr`, `MirStmt` | `rill-mir` |
| `kea-codegen` | Cranelift compilation | `JitCompiler`, `CodegenCtx` | `rill-codegen` |
| `kea-eval` | Tree-walking evaluator (bootstrap/testing) | `Value`, `RuntimeEnv` | `rill-eval` |
| `kea-diag` | Error reporting, source snippets | `Diagnostic`, `SourceMap` | `rill-diag` |
| `kea-lsp` | Language server protocol | `LspServer` | `rill-lsp` |
| `kea-mcp` | MCP server implementation | `McpServer`, `Tool` | `rill-mcp` |
| `kea-fmt` | Code formatter | `Formatter` | `rill-fmt` |
| `kea-test` | Test harness and utilities | `TestHarness` | new |

### Dependency Flow

```
Leaf crates (no kea deps): kea-ast, kea-types, kea-diag

kea-syntax   --> kea-ast
kea-infer    --> kea-ast, kea-types
kea-hir      --> kea-ast, kea-types, kea-infer
kea-mir      --> kea-hir, kea-types
kea-codegen  --> kea-mir, kea-types
kea-eval     --> kea-ast, kea-infer, kea-syntax, kea-types
kea-fmt      --> kea-ast, kea-syntax
kea-lsp      --> kea-syntax, kea-ast, kea-types, kea-infer, kea-eval, kea-diag
kea-mcp      --> kea-syntax, kea-ast, kea-types, kea-infer, kea-eval, kea-diag
kea (binary) --> everything
```

Cross-cutting: `kea-diag` used by most crates. `kea-types` used by most crates. The pipeline is linear — **codegen should never import from the parser, the parser should never import from the type checker.**

---

## Development Workflow

### Prerequisites

- Rust stable (edition 2024)
- mise (task runner)

### Commands

```bash
mise run check        # Fast check: clippy for changed crates (workspace fallback on root Cargo changes).
mise run check-full   # Slow checkpoint: workspace lint + tests + doctests.
mise run test-changed # Run tests only for changed crates (workspace fallback on root Cargo/tooling changes)
mise run test-fast    # Run fast unit/bin tests
mise run test-soak    # Run low-parallelism workspace tests (memory-safe soak profile)
mise run test         # Run workspace lib/test/bin tests
PKG=kea-infer mise run test-pkg # Run all tests for one crate (lib/tests/bin)
mise run test-doc     # Run rustdoc doctests
mise run sccache-stats # Show cache hit/miss stats
mise run sccache-zero # Reset cache stats counters
mise run nextest-install # Install cargo-nextest if missing
mise run fmt          # Format all Rust code
mise run lint         # Run full-workspace clippy on all targets
scripts/cargo-agent.sh test -p kea-eval --lib # Raw cargo with agent-scoped target dir
```

`mise` tasks auto-enable `sccache` when available (`RUSTC_WRAPPER=sccache`); they fall back automatically when it is not installed. Cargo commands run through `scripts/cargo-agent.sh`, which assigns an agent-scoped `CARGO_TARGET_DIR` and then serializes per target via `scripts/with-rust-cache.sh` to avoid lock contention and memory spikes.

### Rules

- **Always run `mise run check` after making changes.** This keeps the inner loop fast while enforcing lint quality.
- **Default runtime inner loop:** `mise run check` -> `mise run test-changed` -> `PKG=<crate> mise run test-pkg` as needed.
- **Run `mise run test-fast` when you need broad but quick workspace signal** (unit/bin targets only).
- **Use `mise run test-soak` for unstable/high-memory periods** (multiple agents, or after lock/memory incidents).
- **Run `mise run test` when changing runtime behavior across crates** (typeck/eval/parser/lowering semantics) or when `test-changed` is too narrow.
- **Run `mise run test-doc` when changing doc comments or doctest extraction.**
- **Keep `cargo-nextest` installed locally** (`mise run nextest-install`) so all test tasks use nextest fast-paths.
- **Default resource caps are intentional:** `KEA_TEST_THREADS` defaults to 2 and `CARGO_BUILD_JOBS` is capped at 6 (override only when you have measured headroom).
- **Do not disable cargo serialization by default.** `KEA_CARGO_SERIALIZE=0` is only for controlled experiments.
- **When running raw `cargo` commands in parallel agent sessions, use `scripts/cargo-agent.sh ...`** (or set a unique `CARGO_TARGET_DIR`) to avoid contention on Cargo's `target/.cargo-lock`.
- **Do not run broad raw tests from repo root** (`cargo test`, `cargo nextest run`, or `--workspace`) unless intentionally doing a full suite.
- **Run `mise run check-full` at checkpoints** (before commits, before handing off work, and before opening/updating a PR).
- **Use fast vs slow cadence deliberately:** `check` + `test-changed` during active iteration, `test-fast` between chunks, `test` for broader behavior changes, `check-full` before hand-off.
- **Default to targeted test commands first** (`test-changed`, `test-pkg`) before full workspace runs.
- **Batch work between slow runs:** prefer bundling multiple logical commits/chunks behind `check` + targeted tests, then run one `check-full` for the batch checkpoint.
- **Never use `cargo build` alone** to verify correctness.
- **Never `git add -A`.** Be intentional. Only stage files you changed.
- **Never commit generated files**, build artifacts, or editor configs.
- **One logical change per commit.** Use [Conventional Commits](https://www.conventionalcommits.org/): `type: imperative description`. Explain "why" not "what". Types:
  - `feat:` — new language feature or capability
  - `fix:` — bug fix
  - `docs:` — documentation only
  - `refactor:` — code change that neither fixes a bug nor adds a feature
  - `test:` — adding or updating tests
  - `proof:` — Lean formalization work
  - `chore:` — build, CI, tooling, dependencies

---

## Coding Conventions

### Rust Style

- Follow standard Rust conventions (`rustfmt`, `clippy`).
- Use `thiserror` for error types in library crates.
- Use `miette` or `ariadne` for user-facing diagnostics in `kea-diag`.
- Use `Arc` for shared data across threads, `Rc` for single-thread sharing. Never raw pointers.
- All public types get doc comments. Internal types get comments explaining "why."

### Kea Style

These conventions apply to all `.kea` source: stdlib, examples, tests.

- **Indentation-sensitive syntax.** No braces, no semicolons. Blocks are delimited by indentation (Python/Haskell style).
- **Dot syntax for method calls.** `xs.map(f)` is sugar for `List.map(xs, f)`. Use Universal Method Syntax (UMS) — any function whose first parameter matches the receiver type can be called with dot syntax.
- **Qualified dispatch with dot.** `xs.Trait.method()` when disambiguation is needed. PascalCase after dot = namespace step (lexical rule). No `::` turbofish — dot is dot.
- **`$` for receiver placement.** `xs.map($.field)` places the receiver at the `$` position.
- **No pipe operator.** Dot syntax + `$` replaces pipes. Chain with dots.
- **`case` for pattern matching.** Prefer `case` over nested `if/else` for multi-branch logic.
- **Effects are explicit.** Functions that perform effects declare them: `fn read() -> String -[IO]>`. Handler blocks delimit effect scope.

### Error Handling

- Library crates return `Result<T, CrateSpecificError>`.
- The CLI crate converts to user-facing diagnostics via `kea-diag`.
- Use `?` propagation. No `.unwrap()` except in tests. No `.expect()` in library code.

### Naming

- Crate names: `kea-{component}` (kebab-case)
- Module names: `snake_case`
- Types: `PascalCase`. Traits: `PascalCase`. Functions: `snake_case`
- AST nodes: `Expr`, `Decl`, `Pattern` (not `Expression`, `Declaration`)
- IR prefixes: `Hir` for HIR, `Mir` for MIR

### Testing

- Unit tests in the same file (`#[cfg(test)] mod tests`)
- Integration tests in `tests/` using `.kea` source files
- Snapshot tests via `insta` for parser output, type inference results, and diagnostic messages
- Property tests via `proptest` for the type inference engine and effect system
- Every bug fix gets a regression test

---

## Architecture Principles

1. **Crate boundaries are API boundaries.** Each crate has a clear public interface. Crates should not reach into each other's internals.

2. **The pipeline is linear.** Source -> tokens -> AST -> HIR -> MIR -> Cranelift IR -> machine code. No backward dependencies. Cross-cutting concerns (diagnostics, spans, types) get their own crate.

3. **Cannibalise aggressively.** Rill's infrastructure is battle-tested. When adapting a rill crate, start by copying it wholesale, then modify. Don't rewrite from scratch what already works.

4. **Types are the source of truth.** The type system drives codegen decisions, effect inference, handler resolution, and safety checks.

5. **Error messages are a feature.** Diagnostic quality is a first-class concern, not polish applied later. `kea-diag` exists from day one. Row polymorphism errors and effect errors must explain problems in plain language, never expose unification variables.

6. **Effects are the novel core.** Algebraic effects with handlers are what distinguishes Kea. The effect system must be correct, ergonomic, and well-integrated from the start. Don't defer effect work — it touches everything.

7. **Struct-everything modules.** No bare functions at module level. Modules are singleton structs. This unifies the namespace and makes UMS work naturally.

---

## Testing Strategy

### Unit Tests

Each crate has unit tests for its internal logic:

- `kea-syntax`: tokenization, indentation handling, parser output for each syntax form
- `kea-types`: type representation invariants, row operations
- `kea-infer`: unification cases, row constraint solving, effect inference, error case coverage
- `kea-eval`: evaluator execution, value representation, effect handling

### Integration Tests (`tests/`)

Whole-program tests: `.kea` source file -> expected output or expected error.

```
tests/
  basic/       # Literals, arithmetic, let bindings
  functions/   # Functions, closures, pattern matching
  types/       # Type inference, row polymorphism, GADTs
  effects/     # Effect declarations, handlers, resumptions
  structs/     # Struct definitions, UMS, methods
  errors/      # Expected diagnostics (snapshot tests)
```

### Snapshot Tests

Use `insta` for:
- Parser AST output (exact structure, especially indentation handling)
- Type inference results (inferred types including effects)
- Diagnostic messages (exact formatting — error messages are a feature)

### Property Tests

Use `proptest` for:
- Type inference: randomly generated expressions should either typecheck or produce a valid error
- Row operations: adding then removing a field should round-trip
- Unification: substitution application should be idempotent
- Effect rows: effect inference should be monotonic

---

## Development Phases

See `docs/spec/ROADMAP.md` for the full plan. See `BRIEFS/INDEX.md` for current status. Summary:

### Phase 0: Bootstrap through Codegen — IN PROGRESS

| Sub-phase | Status | What |
|-----------|--------|------|
| 0a: Lexer + Parser | **done** | Indentation-sensitive lexer/parser, snapshot corpora, property tests |
| 0b: Type System Core | **done** | HM inference, Rémy row unification (records + effects), traits, UMS, kind system |
| 0c: Effect Handlers | **active** | `effect` declarations, `handle`/`resume`, handler typing, `Fail` sugar |
| 0d: Codegen — Pure Subset | ready | Cranelift backend, struct/enum layout, pattern matching, refcounting |
| 0e: Runtime Effects | ready | Handler compilation strategy, IO runtime, Fail optimised path |
| 0f: Memory Model | design | Unique T, borrow convention, reuse analysis |
| 0g: Advanced Types | design | GADTs, Eff kind, associated types, supertraits |
| 0h: Stdlib + Errors | design | @derive, full stdlib, error message investment |

**Parallel track (weeks 2-6):** Tree-sitter grammar, formatter, basic LSP, Neovim plugin.

### Phase 1-3: Self-hosting, Ecosystem, Production

Not yet briefed. See ROADMAP.md.

---

## Agent Guidance

### Before Starting

1. Read `BRIEFS/INDEX.md` for project work status (what's active, ready, blocked)
2. **Read the Cross-Cutting Requirements table at the top of INDEX.md.** Some briefs define constraints that apply across multiple phases. If you're implementing 0d or 0e, you must also read the performance/backend strategy and testing briefs. Ignoring cross-cutting requirements means rework.
3. Read `docs/INDEX.md` for design context
4. **Check `/Users/chris/Projects/rill` for existing code to cannibalise.** This is not optional. Before writing anything from scratch, look at the corresponding rill crate. The rill codebase has battle-tested implementations of most things Kea needs — row unification, type inference, Cranelift codegen, diagnostics, LSP, MCP, formatting. Copy first, then adapt. See "Cannibalising Rill" below for the process.
5. Check the current phase (above)
6. Look at existing tests to understand current capabilities
7. Look for similar patterns in the existing kea codebase

### Work Ethic

When given a task, carry it through to completion. Don't stop to ask for permission to continue unless you genuinely need input or need to communicate something important. Aim for vertical movement — deep progress on the current workstream — rather than horizontal ruts of diminishing value. Make sure you have sufficient supporting work (tests, brief updates) but don't gold-plate. Check in your work as you go.

**Be ambitious.** Rill was 1,088 commits in 17 days — from nothing to a working language with type inference, codegen, MCP, LSP, and formatter. Kea cannibalises most of that. If something can be done correctly now, do it now. Don't create artificial phase boundaries or defer work that's ready to land. When you finish one brief, pick up the next unblocked one. The pace is the point.

### Formal-Only Workstream Protocol

When the active task is explicitly scoped to formalization files (`formal/`, `FORMAL.md`, formal briefs):

1. Continue without interruption if unrelated non-formal files are dirty.
2. Stage and commit only formalization files plus required formal tracking docs.
3. Do not pause to ask about unrelated non-formal diffs unless they block formal work directly.
4. Pause only for:
   - a confirmed Lean↔MCP semantic divergence,
   - a formal proof/build blocker that cannot be resolved locally,
   - or an explicit user redirect.

### Test-First Development

Write the test before the implementation. For the type system especially, define the expected behavior in tests, then make the tests pass. This prevents drift between spec and implementation.

### Type System Work

The type system (`kea-types`, `kea-infer`) requires coherent, holistic design. Do not add features piecemeal. When modifying type inference:

1. Understand the full unification algorithm first
2. Write property tests for the invariants you expect
3. Check that existing tests still pass
4. Verify error messages haven't degraded

### Effect System Work

Effects touch everything — types, inference, codegen, runtime. When working on effects:

1. Read `docs/spec/KERNEL.md` §10 (Effects) and §11 (Handlers) thoroughly
2. Ensure effect rows compose correctly with record rows
3. Test handler scoping — effects must not leak past their handler
4. At-most-once resumption is a hard constraint, enforce it statically

### Parallelizable Work

These can be worked on independently:
- Lexer/parser improvements (`kea-syntax`)
- Diagnostic formatting (`kea-diag`) — given a stable error type interface
- LSP features (`kea-lsp`) — given a stable compilation API
- Formatter (`kea-fmt`) — given a stable AST

### Non-Parallelizable Work

These require coordination:
- Type system changes affect everything downstream (HIR, MIR, codegen, evaluator)
- AST changes affect the parser, type inference, and all IRs
- Effect system changes affect type inference, handlers, and codegen

### Cannibalising Rill

**Rill is Kea's primary codebase asset.** Do not write from scratch what Rill already has. The rill codebase at `/Users/chris/Projects/rill` contains 46K lines of type inference, 12K lines of parser, 3.3K lines of type representations, 2.3K lines of Cranelift codegen, and 1 MB of Lean proofs — all battle-tested. Writing equivalent code from scratch when it exists in rill is a waste.

**Before implementing any feature:** read the corresponding rill code. Understand how rill solved the problem. Then decide: copy and adapt, or use as structural reference. Default to copying.

When adapting a rill crate for kea:

1. **Copy the crate wholesale** into `crates/kea-{name}/`
2. **Rename** rill -> kea in Cargo.toml, module names, types
3. **Remove** rill-specific features (DataFusion, DataFrame, SQL, actors, Python interop)
4. **Extend** with kea-specific features (effects, handlers, indentation, UMS, `$`)
5. **Run tests** after each step to catch breakage early

Key crates to cannibalise:
- `rill-types` → `kea-types` (add Effect, Handler types)
- `rill-infer` → `kea-infer` (add effect inference)
- `rill-syntax` → `kea-syntax` (rewrite parser for indentation)
- `rill-ast` → `kea-ast` (adjust for kea's syntax)
- `rill-eval` → `kea-eval` (add effect handling)
- `rill-diag` → `kea-diag` (mostly as-is)
- `rill-codegen` → `kea-codegen` (Cranelift backend)
- `rill-mcp` → `kea-mcp` (adjust tools)
- `rill-lsp` → `kea-lsp` (adjust for kea)
- `rill-fmt` → `kea-fmt` (adjust for indentation syntax)

### Briefs and Workboard

The `BRIEFS/` directory is the project's task and design tracking system. **Read `BRIEFS/INDEX.md` first** — it's the single-file workboard showing all work by status.

#### Structure

```
BRIEFS/
  INDEX.md          # Workboard — read this first
  in-progress/      # Currently being worked on
  todo/             # Designed, approved, ready to implement
  design/           # Needs more design work
  done/             # Completed — kept for design rationale
```

#### Brief header convention

Each brief is a markdown file. The first lines should follow this pattern:

```markdown
# Brief: Short Title

**Status:** active | ready | design | done
**Priority:** v1-critical | v1 | post-v1
**Depends on:** effect-inference, row-unification
**Blocks:** handler-codegen, effect-polymorphism
```

The body contains motivation, design, implementation plan, and testing requirements. Briefs are design docs, not tickets — they should have enough context for an agent to implement the work without external guidance.

#### At session start

1. Read `BRIEFS/INDEX.md` for the bird's-eye view
2. If picking up active work, read the specific brief and its `## Progress` section
3. Check the dependency graph at the bottom of INDEX.md

#### Working on a brief

1. **Move the file to `in-progress/`** when you start working on it
2. **Add a `## Progress` section** at the end of the brief if one doesn't exist. Update it as you work:
   ```markdown
   ## Progress
   - 2026-02-26: Effect row unification — DONE (commit abc123)
   - 2026-02-25: Pre-impl fixes landed
   - **Next:** Handler type checking
   ```

#### Completing a brief

1. **Move the file to `done/`** when the work is complete
2. Update INDEX.md (move entry from Active to Done, check if anything is unblocked)

#### Creating a new brief

1. Write the brief in the appropriate directory (`todo/` if implementation-ready, `design/` if not)
2. Add an entry to the appropriate section of INDEX.md
3. Note any dependency relationships in the brief header and INDEX.md dependency graph

#### Rules

- **INDEX.md is the view, briefs are the content.** INDEX.md has one-line summaries with links. The brief has the full design.
- **Don't duplicate brief content in INDEX.md.** A brief's summary in INDEX.md should be 1-2 sentences max.
- **Update INDEX.md atomically with brief moves.** If you move a file, update the index in the same commit.
- **Keep briefs concise at the top.** Long briefs cause context rot. Put detailed rationale in a "Design decisions" section at the end. The first screen of a brief should answer: what, why, and what's the implementation plan.
- **Progress sections are append-only** during active work. Don't rewrite history.
- **Use timestamps in progress entries.** Format: `YYYY-MM-DD HH:MM:` (24h, local time). Not just the date — intra-day sequencing matters when multiple agents are working in parallel.

### When Unsure

- Check the relevant doc in `docs/` or `docs/spec/` for design intent
- Check the rill codebase at `/Users/chris/Projects/rill` for reference implementations
- Look for similar patterns in existing code
- If a decision seems to conflict with the docs, flag it rather than making an assumption
