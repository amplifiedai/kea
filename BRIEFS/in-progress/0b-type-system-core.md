# Brief: Type System Core

**Status:** active
**Priority:** v1-critical
**Depends on:** 0a-lexer-parser (needs AST definitions)
**Blocks:** 0c-effect-handlers, 0d-codegen-pure, everything downstream

## Motivation

The type system is Kea's backbone. HM inference with Rémy row
polymorphism for both records and effects, the trait system, and
UMS resolution all need to work before anything else can build
on top. This is the highest-leverage cannibalisation target —
rill-infer is 46K lines of battle-tested inference engine with
extensive property tests.

## What transfers from Rill

**rill-types** (3,310 LOC):
- `Type` enum, `RowType`, `TypeVarId`, `RowVarId` — direct transfer
- `Substitution` type and operations — direct transfer
- `Kind` system — direct transfer, extend with `Eff` kind
- Remove: `DataFrameType`, `ColumnType`, `SqlType`, `ActorType`,
  `DimensionType`, `AggregateType`
- Add: `EffectRow` (new row kind using same `RowType` machinery),
  `HandlerType`, `UniqueType`, effect set representation

**rill-infer** (46,268 LOC):
- `lib.rs` (4,098 LOC): Unifier, provenance tracking, variable
  allocation — direct transfer. This is the Rémy row unification
  engine. It works for records; extending it to effects means
  adding a second row kind that uses the same algorithm.
- `typeck.rs` (19,016 LOC): Expression-level HM inference with
  let-generalisation — structural transfer. Large parts copy
  directly (literal checking, binary ops, let bindings, lambda
  inference, pattern matching). Parts that need rewriting: module
  resolution (struct-everything instead of bare functions), method
  dispatch (UMS instead of pipes), effect tracking.
- `exhaustive.rs` (357 LOC): Exhaustiveness checking — direct
  transfer.
- `trace.rs` (175 LOC): Compiler tracing — direct transfer.
- `prop_tests.rs` (4,554 LOC): Property tests — transfer and
  extend for effect rows. These are gold. They catch bugs that
  unit tests don't.
- `typeck_tests.rs` (18,068 LOC): Unit tests — use as reference
  for test patterns. Rewrite test cases for Kea syntax.

**rill-diag** (341 LOC):
- Should already exist from 0a. Diagnostic categories may need
  extending for effect-related errors.

## What's new (not in Rill)

1. **Effect rows.** Same Rémy unification algorithm, new row kind.
   An effect row `[IO, Fail E | e]` is structurally identical to
   a record row `{ io: IO, fail: Fail E | r }` from the
   unifier's perspective. The key insight: we don't need a new
   unification algorithm, we need to apply the existing one to
   a new domain.

2. **Explicit signatures on all `fn` (KERNEL §5.1).** All `fn`
   definitions require full signatures — parameter types, return
   type, and effect annotation. `->` is pure (empty effect row).
   `-[e]>` is effectful. Closures remain fully inferred. For `fn`,
   inference is verification: check the body against the declared
   signature and error if the body performs effects not in the
   declaration. This is the opposite of "infer then compare" —
   the signature is the source of truth.

3. **Struct-everything scoping.** Name resolution must handle:
   - Inherent methods (defined inside struct block)
   - Singleton module functions (struct with no fields)
   - Nested types (`Parent.Child`)
   - `Type as Trait` implementation blocks
   - Prelude traits (Appendix C) always in scope

4. **UMS resolution** (CALL-SYNTAX.md):
   - `expr.method(args)` → inherent first, then trait search
   - `expr.Qual::method(args)` → qualified dispatch
   - `$` receiver placement
   - Field vs method: no parens = field, parens = method

5. **Labeled and positional parameters** (KERNEL §10.2):
   - `_` prefix marks positional params
   - Labeled params are passed by name at call site
   - Receiver fills first `_` param (or `$` position)

6. **Kind system: `*` + `Eff` only (KERNEL §6.6).** No `* -> *`.
   No higher-kinded type parameters. A type parameter used in
   effect position (`-[E]>`) is inferred to have kind `Eff`. All
   other type parameters have kind `*`. Kind errors when a
   parameter is used inconsistently (as both type and effect row).

7. **Effect row aliases (KERNEL §11.5).** `type DbEffects =
   [IO, Fail DbError]` — type aliases that expand to effect rows.
   The type checker must handle alias expansion in effect position.
   Parameterised aliases: `type WithDb e = [IO, Fail DbError, e]`.

## Implementation Plan

### Step 1: kea-types crate

Copy rill-types wholesale. Then:
- Rename rill → kea everywhere
- Remove DataFrame/SQL/Actor/Dimension/Aggregate types
- Add `EffectRow` variant (or extend existing `RowType` with a
  row kind discriminator)
- Add `HandlerType` for handler expressions
- Add effect set representation on `FunctionType`
- Keep `Substitution`, `TypeVarId`, `RowVarId`, `Kind` as-is
- Verify: `cargo test -p kea-types` passes after cleanup

### Step 2: kea-infer crate — unification core

Copy rill-infer's `lib.rs` (unifier, provenance, variable
allocation). Then:
- Rename rill → kea
- Remove rill-specific constraint kinds
- Extend unification to handle effect rows (same algorithm,
  new row kind)
- Port property tests from `prop_tests.rs`, extend with
  effect row properties:
  - Effect row union is commutative
  - Effect row union is idempotent
  - Adding then handling an effect round-trips
  - Lacks constraints propagate correctly for effects

### Step 3: kea-infer crate — type checking

Copy rill-infer's `typeck.rs` structure. This is the biggest
adaptation:
- Literal, binary op, let-binding inference → mostly direct copy
- Lambda inference → add effect row to function type
- Pattern matching → copy exhaustiveness from rill
- **Rewrite:** Name resolution for struct-everything
  - Look up inherent methods in struct scope
  - Look up trait methods from in-scope traits
  - Handle `Type.function()` prefix calls
  - Handle `expr.method()` dot calls (UMS)
  - Handle `expr.Qual::method()` qualified dispatch
- **Rewrite:** Method resolution per CALL-SYNTAX.md
- **New:** Effect checking — for `fn`, check body against declared
  effect signature (signature is source of truth). For closures,
  infer effects bottom-up from body.
- **New:** Kind checking — `*` vs `Eff` consistency. Parameters
  in effect position get kind `Eff`, all others `*`.
- **New:** Effect row alias expansion in type positions
- **New:** Labeled parameter matching at call sites

### Step 4: Tests

- Port rill-infer's property tests, extend for effects
- Write snapshot tests for type checking on Kea source:
  - Pure functions: `->` verified against body
  - Effectful functions: `-[IO]>` verified, error if body
    performs undeclared effects
  - Closures: effects inferred bottom-up
  - Effect-polymorphic higher-order functions: `e` variable flows
  - Row-polymorphic record functions: `{ name: String | r }`
  - Kind checking: `Eff` vs `*` consistency, error on mismatch
  - Effect row aliases: expansion in type positions
  - UMS resolution: dot calls desugar correctly
  - Error cases: ambiguous dispatch, missing method, missing
    trait implementation, undeclared effect in fn body
- Diagnostic snapshot tests: error messages for type errors must
  be human-readable, reference source locations, and never show
  raw type variable IDs

## Testing

- `cargo test -p kea-types -p kea-infer` passes
- Property tests for row unification (records and effects)
- Snapshot tests for inferred types on ~30 representative programs
- Snapshot tests for error diagnostics on ~15 error cases
- Effect inference: functions performing effects get correct
  effect rows
- UMS: dot calls resolve correctly per CALL-SYNTAX.md

## Definition of Done

- Can type-check pure Kea programs with structs, enums, pattern
  matching, row-polymorphic records, traits, and UMS
- All `fn` require explicit signatures; closures fully inferred
- Effect signatures verified against body (undeclared effect = error)
- Effect rows unify using the same algorithm as record rows
- Kind system: `*` + `Eff`, no `* -> *`, kind errors are clear
- Effect row aliases expand correctly
- Property tests cover row unification invariants for both kinds
- Error messages are human-readable with source locations
- `mise run check` passes

## Scope Boundary

**In scope for 0b:** HM inference, Rémy row unification (records
+ effects), trait system (definitions, impls, coherence), UMS
resolution, kind checking (`*` + `Eff`), effect row aliases,
explicit signature verification for `fn`, closure effect inference.

**Deferred to 0g:** Associated types (`type Item` in traits),
supertraits (`where Self: Eq`), GADTs. These are 0g work, though
the trait infrastructure from 0b must be extensible for them.

## Transition Scaffolding (Explicit)

These are temporary compatibility paths during 0b and must be
removed before 0b closes:

- Legacy lattice effect terms (`pure`/`volatile`/`impure`) may
  coexist with row-based effect annotations only while parser/AST
  and contract checks migrate to rows end-to-end.
- Any remaining non-Kea parser/type-system surface inherited from
  rill (pipe parsing, DataFrame/column typing surface, HKT-era kind
  arrows) is compatibility debt, not feature scope for 0b.

Kill point for all of the above: before moving this brief to
`done/`, with removal tracked in `## Progress`.

## 0b Exit Criterion: Delete Lattice Effect Model

The lattice effect model (`EffectLevel { Pure, Volatile, Impure }`,
`EffectTerm`, `EffectConstraint { Eq, Leq, Join }`,
`solve_effect_constraints`, `effects_leq`, and all bridge functions
like `effects_as_row`, `effect_annotation_to_effects`,
`effect_label`) is migration scaffolding from rill. It must be
deleted before this brief moves to `done/`.

**What replaces it:** Effect rows are `RowType` with kind `Eff`.
Effect checking uses the same Rémy row unification as record rows.
The constraint solver for effects is the existing row unifier —
no separate `solve_effect_constraints` needed.

**How to track:** Every lattice function gets a
`// TODO(0b-exit): delete when row-based effect solver is complete`
marker. The exit criterion is: `EffectLevel` enum is deleted from
kea-types, and all effect checking flows through `EffectRow`
unification.

**Legacy syntax handling:** `EffectAnnotation::Pure` desugars to
`EffectRow::pure()` (closed empty row). `EffectAnnotation::Volatile`
and `EffectAnnotation::Impure` emit a deprecation diagnostic —
they have no semantic meaning in the row model and must not be
modelled as fresh open row variables (that would accidentally make
signatures polymorphic). Existing test files using these annotations
should be migrated to row syntax (`->` for pure, `-[IO]>` for
impure) as part of the exit criterion.

## Resolved Questions

- **Effect inference integration:** Integrated into the main HM
  pass. Effect variables are row variables; they participate in
  the same unification. This is the Koka approach.

- **Fail uniqueness:** Enforced in 0b. At most one `Fail E` per
  effect row. When merging effect rows with different `Fail`
  payloads, require unification or `From` conversion to the
  declared type. If neither resolves, emit a diagnostic with help:
  "implement `From ParseError for AppError`" or "use `catch` to
  handle ParseError explicitly." This is a row-level constraint
  (lacks `Fail` on the rest variable after one `Fail` entry).

- **Capability effects (IO, Send, Spawn):** Ordinary effect labels
  in the type system. No special-case type rules. Handlers for
  them type-check normally (enabling test mocks). Direct-call
  compilation is a codegen/runtime optimisation (0e), not a type
  system concern.

## Progress
- 2026-02-26: Moved brief to `in-progress`; starting rill-types/rill-infer cannibalisation for `kea-types` + `kea-infer`.
- 2026-02-26: Bootstrapped `kea-types` + `kea-infer` from Rill into workspace with kea crate naming/dependencies and namespace renames. Verified with `mise run check`, `PKG=kea-types mise run test-pkg` (49/49), and `PKG=kea-infer mise run test-pkg` (721/721).
- 2026-02-26: Added Kea-native effect representation in `kea-types`: `Kind::Eff`, `EffectRow`, and `HandlerType` with display/behavior unit tests. Verified with `PKG=kea-types mise run test-pkg` (54/54) and `mise run check`.
- 2026-02-26: Added `Unifier::unify_effect_rows` and effect-row parity tests/properties in `kea-infer` (`lib.rs` + `prop_tests.rs`) to prove effect rows are solved by the same Rémy row engine and lacks constraints. Verified with `PKG=kea-infer mise run test-pkg` (726/726) and `mise run check`.
- 2026-02-26: Threaded `EffectRow` into function-effect verification diagnostics in `typeck.rs` (declared vs inferred mismatch now reports row-form context alongside lattice labels). Verified with `PKG=kea-infer mise run test-pkg` (726/726) and `mise run check`.
- 2026-02-26: Added AST/parser support for row-style effect annotations (`-[IO, Fail E | e]>`) and threaded compatibility handling through `kea-infer` contract/effect annotation paths. Verified with `PKG=kea-syntax mise run test-pkg` (375/375), `PKG=kea-infer mise run test-pkg` (726/726), and `mise run check`.
- 2026-02-26: Added `kea-infer` regression tests for row-based effect contracts (closed rows accepted, open concrete rows rejected in compatibility mode, tail-only row vars propagated/validated). Verified with `PKG=kea-infer mise run test-pkg` (729/729) and `mise run check`.
- 2026-02-26: Added effect-row alias substrate and tests: AST/Parser now represent `alias X = [ ... ]` via `TypeAnnotation::EffectRow`; contract validation has record-aware alias expansion for declared effect rows, with compatibility rejection for aliases that expand to open rows. Verified with `PKG=kea-syntax mise run test-pkg` (376/376), `PKG=kea-infer mise run test-pkg` (731/731), and `mise run check`.
- 2026-02-26: Added parser coverage for tail-only row form (`-[| e]>`) in function declarations and function type annotations, matching compatibility handling already in `kea-infer`. Verified with `PKG=kea-syntax mise run test-pkg` (378/378) and `mise run check`.
- 2026-02-26: Added explicit `// TODO(0b-exit)` markers across lattice bridge code in `kea-types`, `kea-infer/lib.rs`, and `kea-infer/typeck.rs` (including legacy contract helpers and solver call sites) so 0b exit cleanup is mechanically trackable.
- 2026-02-26: Switched function/trait declared-effect contract checks to row-based subsumption (`declared ~ open(inferred, fresh_rest)`) via row unification, replacing lattice `<=` checks in contract paths. Added row-var instantiation safety to avoid variable ID collisions during subsumption checks.
- 2026-02-26: Added row-level Fail validation in contract paths: duplicate/incompatible `Fail` payload detection, rest-tail lacks-`Fail` constraints during subsumption checks, and mismatch diagnostics with `From`/`catch` guidance.
- 2026-02-26: Added deprecation warnings for legacy `volatile`/`impure` effect annotations in `validate_module_fn_annotations` and added gate tests for row-subsumption behavior, legacy syntax warnings, and duplicate `Fail` diagnostics. Verified with `mise run check` and `PKG=kea-infer mise run test-pkg` (736/736).
- **Next:** Replace remaining lattice-bound expression/callback effect inference paths (`EffectTerm`/`solve_effect_constraints` in `typeck.rs`) with row-native effect checking so `EffectLevel` can be deleted for 0b exit.
