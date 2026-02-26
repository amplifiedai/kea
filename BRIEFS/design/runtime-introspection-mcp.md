# Brief: Semantic Introspection Platform (MCP + Runtime)

**Status:** design
**Priority:** v1
**Depends on:** 0b-type-system-core, 0b-mcp-server, 0d-codegen-pure
**Blocks:** REPL UX, LSP polish consistency, runtime-safe agent tooling, production introspection story

## Motivation

Kea's effect/type system and dispatch rules are valuable beyond type
checking. They can power a **semantic platform API** consumed by
multiple clients:

- LSP and editor tooling
- REPL exploration
- debugger and production diagnostics
- CI/policy checks
- agents (internal and external)

Agents are one consumer, not the product definition. The product
definition is: **one semantic engine, many consumers**.

## Problem Statement

Without a stable semantic API, each tool rebuilds compiler knowledge
ad hoc (or reaches into unstable internals), which causes:

- drift between tooling surfaces (LSP vs REPL vs MCP answers differ),
- compiler evolution lock-in (tooling depends on internal HIR/MIR),
- security/perf issues when runtime introspection is unbounded.

## Core Design

### 1) Two-surface split (hard boundary)

1. **Compiler MCP (dev-time)**
   - Rich semantic queries for development workflows.
   - May evolve faster, but must still be versioned.
   - Can include compile-time artifacts not safe for production.

2. **Runtime Introspection (prod-safe)**
   - Small, stable, bounded, policy-gated.
   - Exposed as a capability effect (`Introspect`), never ambient.
   - No raw compiler internals, no untrusted eval/typecheck.

### 2) Runtime introspection effect (minimal v0)

Conceptual surface:

```kea
effect Introspect
  fn effects_of(_ symbol: Symbol) -> EffectSig
  fn methods_of(_ ty: TypeId) -> List MethodSig
  fn protocol_of(_ ref: Ref M) -> ProtocolSig
  fn graph_summary(_ scope: Scope) -> GraphSummary
```

Notes:
- v0 uses typed actor refs (`Ref M`), not `AnyRef`.
- Response schemas are versioned and size-bounded.
- Results return semantic summaries, not compiler AST/IR.

### 3) Policy-gated runtime handler

```kea
fn Introspect.with_policy(_ policy: IntrospectPolicy, _ f: () -[Introspect, e]> T) -[e]> T
```

Required policy controls:
- allowlist by operation,
- symbol/type/scope allowlists,
- payload/depth/item caps,
- rate limiting and per-caller budgets,
- redaction rules,
- audit mode (`off` | `aggregate` | `full`).

This enforces: **effects guarantee plumbing correctness, runtime policy
guarantees authorization and boundedness**.

### 4) Deterministic semantics for tools and agents

Universal dot resolution and effect signatures must be queryable in
stable form. Tooling and agents should consume the same semantic facts
that the compiler uses for diagnostics.

## Security and Performance Invariants

Must hold for any runtime introspection implementation:

1. Deny-by-default policy in production.
2. All responses have explicit schema version.
3. Bounded query cost (time + size + depth).
4. No secret-bearing raw state by default.
5. No runtime surface for arbitrary code evaluation or full-source dump.
6. All accepted queries can be audited with caller identity and cost.

## Roadmap Slotting

This is a cross-cutting track with staged delivery:

1. **Phase 0b-0d (design + foundation):**
   - Keep compiler MCP moving.
   - Normalize stable semantic IDs and response shapes.
   - Ensure type/effect/dispatch canonicalization is not duplicated.

2. **Phase 0d-0e (early implementation prep):**
   - Build a shared semantic query layer in compiler services.
   - Make LSP/REPL/MCP consume common query contracts where feasible.

3. **Phase 2a (implementation target):**
   - Land runtime-safe introspection effect and policy handler.
   - Ship prod/dev policy presets and audit tooling.
   - Integrate with debugger/ops surfaces.

4. **Phase 3+ (extension):**
   - Richer dynamic summaries for distributed actors.
   - Agent runtime orchestration integrations.

## Implementation Plan (when promoted from design)

1. Define schema package for semantic responses (versioned).
2. Add semantic-query conformance tests across MCP/LSP/REPL.
3. Implement `Introspect` effect + handler contract.
4. Implement policy engine (limits/redaction/audit).
5. Add production-safe defaults and docs.

## Testing Requirements

- Contract tests: identical semantic answers across MCP/LSP/REPL for same source.
- Security tests: policy denies and redactions are enforced.
- Abuse tests: rate/payload/depth caps prevent blow-ups.
- Performance tests: bounded latency under adversarial query patterns.

## Definition of Done (for implementation phase)

- Runtime introspection is capability-gated, bounded, and audited.
- Compiler tooling surfaces share a common semantic contract.
- No runtime exposure of raw HIR/MIR/eval endpoints.
- Prod defaults are deny-by-default with explicit opt-in scopes.
- `mise run check` and targeted tool integration tests pass.

## Non-Goals (v0)

- Full live actor heap/state dumps.
- Arbitrary runtime expression evaluation via introspection.
- Exposing unstable internal compiler IR formats as public runtime API.
- Solving distributed debugging in full (covered by distributed-actors track).

## Open Questions

- Symbol/Type identity stability across incremental builds and package upgrades.
- Redaction defaults for multi-tenant deployments.
- Minimum useful dynamic graph summaries without leaking internals.
