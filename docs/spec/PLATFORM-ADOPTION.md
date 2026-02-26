# Kea Platform And Adoption Strategy

This spec connects language design to product adoption.
It is the "so what" layer across:

- [VISION](../VISION.md)
- [KERNEL](KERNEL.md)
- [ROADMAP](ROADMAP.md)
- [EFFECTS-ORIENTED guide](../EFFECTS-ORIENTED.md)
- [UNIVERSAL-DOT guide](../UNIVERSAL-DOT.md)
- [Runtime introspection brief](../../BRIEFS/design/runtime-introspection-mcp.md)
- [Testing brief](../../BRIEFS/design/testing.md)
- [Distributed actors brief](../../BRIEFS/design/distributed-actors.md)
- [Performance/backend brief](../../BRIEFS/design/performance-backend-strategy.md)

## 1. Product Thesis

Kea is not "effects for effects' sake."
Kea is a semantic platform where one type/effect engine powers many
developer experiences:

- language safety,
- testing ergonomics,
- editor and REPL intelligence,
- machine-readable automation (MCP/CI),
- runtime introspection with policy control.

Agents are one consumer of this platform, not the definition of it.

## 2. What Is Already Captured

The current docs already lock core direction:

- Effects are row-polymorphic and first-class (`KERNEL`).
- Struct-everything + universal dot are language-level (`KERNEL`, `CALL-SYNTAX`).
- Runtime-safe introspection is policy-gated, not ambient (`runtime-introspection-mcp`).
- Testing is language/runtime integrated (`testing`).
- Distributed actor direction avoids distributed refcounting (`distributed-actors`).
- Performance strategy is backend-neutral MIR first, backend choice later (`performance-backend-strategy`).

## 3. Opportunities We Should Not Sleep On

### 3.1 One semantic contract, many tools

Treat semantic queries as a product API consumed by:

- `kea check` / compiler diagnostics,
- LSP,
- REPL,
- MCP tooling,
- test runner reporting,
- debugger/ops surfaces.

Do not allow each tool to invent its own semantic shape.

### 3.2 `kea test` as the adoption wedge

`kea test` should be a primary reason to choose Kea:

- `assert` + `check` dual model,
- expression capture and structural diff,
- effect-aware parallel scheduling,
- deterministic replay and property testing,
- structured output for humans and machines.

If this is excellent, effects become felt value, not theory.

### 3.3 Runtime policy as a first-class capability story

Effects guarantee capability plumbing correctness.
Policy handlers guarantee authorization and boundedness.

This split should be explicit in docs and CLI defaults:

- dev profile: permissive, observable
- test profile: deterministic and replayable
- prod profile: deny-by-default, audited, bounded

### 3.4 Migration playbooks as growth engine

Publish opinionated before/after guides for:

- Python (implicit side effects -> explicit effect contracts),
- TypeScript (runtime shape checks -> typed protocols/effects),
- Go (interface + context patterns -> capability/effect signatures),
- Elixir/Erlang (dynamic OTP -> typed protocols with effects).

Kea adoption will come from concrete migration wins, not theory docs.

### 3.5 Typed OTP positioning with disciplined claims

Compete on guarantees, not runtime mythology:

- typed actor protocols,
- effect-tracked side effects,
- serialization boundaries checked at compile time,
- policy-aware introspection.

Be explicit about non-goals:

- not promising BEAM-equivalent runtime maturity in v1,
- no distributed refcounting,
- no unbounded runtime introspection surfaces.

## 4. Consumer Matrix (Authoritative)

| Consumer | Needs | Source of Truth | Constraints |
|---|---|---|---|
| Compiler/`kea check` | types, effects, diagnostics | semantic query layer | deterministic, stable error codes |
| LSP | hover/completion/definition/effects | semantic query layer | low latency, incremental |
| REPL | interactive type/effect visibility | semantic query layer + runtime | session-scoped, safe defaults |
| `kea test` | assertion semantics + structured results | test runtime + semantic query layer | fast, deterministic replay |
| MCP (dev) | rich machine-readable semantics | compiler MCP surface | versioned, explicit capabilities |
| Runtime introspection | bounded operational summaries | `Introspect` effect handler | policy-gated, audited, capped |
| Agents (external/internal) | safe semantic affordances | same contracts as above | no privileged backdoor APIs |

## 5. Required Platform Invariants

1. Same source, same semantic answer across compiler/LSP/REPL/MCP.
2. Stable schema versions for machine consumers.
3. Runtime introspection is deny-by-default in production.
4. Query cost is bounded (payload/depth/rate/time budgets).
5. Redaction and audit are part of the default runtime posture.
6. No raw HIR/MIR exposure in runtime introspection.
7. Test result format is stable and machine-consumable.

## 6. Roadmap Slotting

### Phase 0b-0d

- Establish semantic query contracts and conformance tests.
- Keep compiler MCP useful while avoiding internal-shape lock-in.
- Ensure `kea check`, LSP, and REPL share semantic answers.

### Phase 0d-1

- Land `kea test` as first-class UX (speed + clarity + replay).
- Publish migration playbooks in user-facing docs.
- Define prod/dev/test policy profiles for introspection.

### Phase 2a

- Ship runtime-safe introspection (`Introspect` effect + policy engine).
- Integrate debugger/ops and MCP consumption against the same contracts.

### Phase 2-3

- Extend to distributed actor operational summaries.
- Evaluate backend options by benchmark data, not narrative.

## 7. Immediate Documentation Work

1. Keep [EFFECTS-ORIENTED.md](../EFFECTS-ORIENTED.md) focused on migration outcomes.
2. Keep [UNIVERSAL-DOT.md](../UNIVERSAL-DOT.md) focused on readability, dispatch clarity, and refactoring ergonomics.
3. Tie both guides to this platform page and to `kea test`.
4. Keep claims about OTP/performance bounded and benchmark-coupled.

## 8. Definition Of Success (v1)

Kea is perceived as:

- practical and fast to iterate,
- unusually strong at testability and observability,
- safe for capability-constrained systems,
- coherent across CLI/editor/REPL/MCP/runtime tooling.

If users feel these outcomes directly, the effect system has broken
through.
