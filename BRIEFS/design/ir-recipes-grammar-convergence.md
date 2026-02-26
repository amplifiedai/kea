# Brief: IR–Recipes–Grammar Convergence

**Status:** design
**Priority:** Phase 1-2 (self-hosting prerequisite)
**Depends on:** 0d-codegen-pure (bootstrap IR exists), 0g-advanced-types (associated types for Grammar/Recipe traits), packaging-ffi-comptime (Compile effect)
**Blocks:** self-hosting compiler, third-party backend ecosystem, recipe ecosystem

## Motivation

KERNEL §15 specifies that Kea's compiler IRs are Kea types and
compiler passes are pure Kea functions. This is not a vague aspiration —
it's a load-bearing design decision that unifies three mechanisms:

1. **Typed Grammar Interface** — `embed <Grammar> { ... }` for
   domain syntax (HTML, SQL, CSS)
2. **Compiler Recipes** — `@derive`, `@gpu`, `@sql`, user-defined
   compile-time transformations over StableHIR
3. **Backend Interface** — Cranelift, LLVM, Kea-native as
   implementations of a MIR → target lowering contract

All three are compile-time functions running under the `Compile`
effect that transform typed IR. They share the same trait interface,
the same capability model, and the same stability contract.

## The Convergence

### Grammar = Recipe = Backend

```
Grammar trait:    parse(src) → check(ast, ctx) → lower(typed) → LoweredExpr
Recipe:           receive(StableHIR) → validate(constraints) → transform(hir) → StableHIR
Backend:          receive(MIR) → validate(target_constraints) → lower(mir) → TargetCode
```

These are the same shape: `input → validate → output`, all under
`Compile`. The difference is input type and output type:

| Extension kind | Input | Output | Stability tier |
|----------------|-------|--------|----------------|
| Grammar | Source text | LoweredExpr (Kea IR) | Grammar contract versioned |
| Recipe | StableHIR nodes | StableHIR nodes | StableHIR versioned (§15.1) |
| Backend | UnstableMIR | Target machine code | UnstableMIR may break (§15.1) |
| Restricted sublanguage | StableHIR subset | Custom backend output | Recipe-defined |

### Row Polymorphism as Versioning

StableHIR is row-extensible (§15.1). When the compiler adds a new
IR node (say, a new expression form), existing recipes see it as
part of the row variable — they don't break. This is the same
mechanism that makes record types and effect rows extensible:

```kea
-- A recipe that works on any HIR with at least these nodes
fn simplify(expr: HirExpr { Let: _, If: _, Call: _ | r }) -> HirExpr { Let: _, If: _, Call: _ | r }
  -- handles Let, If, Call; passes through everything else via r
```

New nodes (e.g., `Match`, `Handle`) are absorbed by `r`. The recipe
is forward-compatible without modification. This is why row
polymorphism is load-bearing for the recipe/extension ecosystem.

### Restricted Sublanguages are Grammars

§15.2 defines restricted sublanguages: subsets of Kea with no
closures, no recursion, no heap — for lowering to GPU/FPGA/SQL
backends. These are validated by recipes:

```kea
@gpu
fn matmul(a: Matrix Float, b: Matrix Float) -> Matrix Float
  -- body must conform to GPU-restricted grammar
```

The `@gpu` recipe:
1. Receives the function's StableHIR
2. Validates it conforms to the restricted grammar (no closures, etc.)
3. Lowers through a GPU-specific backend (MLIR, StableHLO, PTX)

This IS a Grammar implementation. The Grammar trait's `check` step
validates the restriction. The `lower` step produces target code.
The `Compile` effect governs execution.

## IR Stability Tiers (KERNEL §15.1)

| Tier | Audience | Stability | Example consumer |
|------|----------|-----------|-----------------|
| **StableHIR** | Recipe authors, linters, formatters | Versioned, row-extensible | `@derive`, `@gpu`, user macros |
| **UnstableMIR** | Backend authors, power users | May break between minor versions | Cranelift backend, LLVM backend |
| **InternalIR** | Compiler developers only | Private, no promise | Bootstrap Rust HIR/MIR types |

**Bootstrap note:** The 0d HIR/MIR implemented in Rust are InternalIR.
They become the substrate for StableHIR/UnstableMIR when Kea
self-hosts. The types don't change — they get stability annotations
and row-polymorphic interfaces.

## Design Requirements

### Unified Extension Trait

The Grammar and Recipe traits should share a common base or be
structurally compatible:

```kea
trait Grammar
  type Ast
  type Out
  type Err
  fn parse(src: String) -[Compile]> Result(Self.Ast, Self.Err)
  fn check(ast: Self.Ast, ctx: GrammarCtx) -[Compile]> Result(Typed(Self.Out), Diag)
  fn lower(typed: Typed(Self.Out)) -[Compile]> LoweredExpr

trait Recipe
  type Input    -- StableHIR node type (row-polymorphic)
  type Output   -- transformed IR or target code
  fn validate(input: Self.Input, ctx: RecipeCtx) -[Compile]> Result(Self.Input, Diag)
  fn transform(input: Self.Input) -[Compile]> Self.Output
```

Both run under `Compile`. Both produce diagnostics through `kea-diag`.
Both are capability-gated (no filesystem, no network at compile time
unless explicitly granted).

### Effect-Gated Compile Capabilities

Recipes and grammars run under the `Compile` effect, which
provides controlled access to:
- IR introspection (read types, read effect rows)
- Code generation (emit new declarations)
- Diagnostic emission
- Module metadata queries

They do NOT have access to `IO`, `Net`, etc. unless explicitly
granted in the package manifest. This is the effects-as-policy
model applied to the compiler itself.

### Tooling Integration

All three extension kinds (grammar, recipe, backend) produce
diagnostics through the same `kea-diag` path. LSP, MCP, REPL,
and CI consume them uniformly. No side-channel formats.

## Relationship to Other Briefs

- **[typed-grammar-interface](typed-grammar-interface.md)** — defines
  the Grammar trait and the `embed` syntax. This brief shows that
  Grammars and Recipes converge.
- **[packaging-ffi-comptime](packaging-ffi-comptime.md)** — defines
  the `Compile` effect and comptime execution model. Both Grammar
  and Recipe run under `Compile`.
- **[performance-backend-strategy](performance-backend-strategy.md)** —
  defines the backend interface trait. This brief shows that backends
  are a kind of Grammar over MIR.
- **[0d-codegen-pure](../in-progress/0d-codegen-pure.md)** — builds
  the bootstrap InternalIR (Rust HIR/MIR types). This brief defines
  the self-hosted future of those types.
- **KERNEL §15** — the normative specification for recipes and IR
  stability tiers.

## Implementation Plan (when promoted)

### Phase 1: StableHIR contract

1. Define StableHIR as row-polymorphic Kea types
2. Implement `@derive` as a recipe consuming StableHIR
3. Validate that row extensibility works (add a new HIR node,
   verify existing recipes don't break)

### Phase 2: Recipe ↔ Grammar unification

1. Refactor Grammar and Recipe to share the Compile capability model
2. Implement a restricted sublanguage as both a Recipe and a Grammar
3. Validate tooling integration (diagnostics, LSP, MCP all work)

### Phase 3: Backend as Grammar

1. Implement second backend (LLVM or Kea-native) using the unified
   Grammar/Recipe interface over UnstableMIR
2. Validate that the backend interface trait and Grammar trait converge
3. Benchmark: second backend matches Cranelift quality on core suite

## Definition of Done

- StableHIR is a versioned, row-extensible Kea type
- `@derive` works as a recipe over StableHIR
- At least one restricted sublanguage validates via recipe
- Grammar and Recipe share the Compile capability model
- Backend interface is structurally compatible with Grammar trait
- Row-extensibility proven: adding HIR node doesn't break existing recipes

## Open Questions

- Should Grammar and Recipe be the same trait with different
  associated types, or two traits with a shared Compile capability?
  (Proposal: two traits. The input shapes are different enough
  that a single trait would be awkward. But they share Compile.)
- How do we version StableHIR across compiler releases?
  (Proposal: semver on the HIR crate. Row extensibility handles
  additive changes. Breaking changes bump the major version.)
- Should UnstableMIR be exposed to third-party backends at all,
  or should backends target StableHIR and let the compiler handle
  MIR lowering? (Proposal: expose UnstableMIR with explicit
  instability warning. Power users want it. The Rust ecosystem
  model of "unstable but available" works.)
