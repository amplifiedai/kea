# Brief: Revision-Preserving Type Evolution

**Status:** design (post-v1)
**Priority:** Phase 2+ (requires ecosystem of recipes/grammars targeting StableHIR)
**Depends on:** ir-recipes-grammar-convergence, typed-grammar-interface, self-hosting compiler
**Blocks:** non-breaking StableHIR field widening, general library API evolution

## Motivation

Row polymorphism handles **additive** IR and API changes: new enum
variants, new record fields. These are absorbed by row variables
automatically. Version tags handle **breaking** changes: removed
fields, incompatible type changes. These force a hard boundary
between versions.

There's a third category that neither mechanism addresses:
**widening** an existing field's type. Example: `Let.name` changes
from `String` to `Pattern` where `String` is a subtype of `Pattern`
(every string is a trivial pattern). All existing IR nodes remain
valid. All existing passes that assume `name: String` are still
correct — for the inputs they were designed to handle. But the
wider type means new inputs can appear that existing passes don't
handle.

This problem isn't unique to compiler IR. Every library that ships
a public struct type will eventually want to widen a field. The
compiler should not be special — if it needs revision-safe evolution,
every library author should have the same mechanism.

## The Insight: Revision Preservation

José Valim's work on [data evolution with set-theoretic types]
(https://dashbit.co/blog/data-evolution-with-set-theoretic-types)
identifies a clean solution: **revisions** with a **preservation
property**.

### How it works in set-theoretic types

Each revision of a struct widens zero or more fields. The
constraint: each revision must be a supertype of the previous.

```
revision 1: name :: String
revision 2: name :: String | Pattern
```

For a function `f(schema) -> schema`, the compiler generates
intersection-typed signatures:

```
f(r1_input) -> r1_output
f(r2_input and not r1_input) -> r2_output
```

**Revision preservation property:** if you give `f` an r1 value,
you get back an r1 value. If you give it an r2 value, you get
back an r2 value. Existing code doesn't break because r1 inputs
still produce r1 outputs. New code handling r2 inputs can produce
wider outputs.

The compiler derives these signatures automatically from revision
annotations. Library authors write `f(Schema) -> Schema` and the
compiler handles the rest.

### What Elixir has that Kea doesn't

Set-theoretic types give Elixir three operations Kea lacks:

1. **Union types** (`String | Nil`) — Kea has enum variants but
   not arbitrary type unions.
2. **Intersection types** (`f(r1) -> r1 & f(r2) -> r2`) — Kea
   doesn't have intersection function types.
3. **Negation types** (`r2 and not r1`) — required to isolate
   "the new part" of each revision.

### What Kea has that could substitute

Row polymorphism provides structural extensibility that
set-theoretic types don't have. The question is whether rows +
some revision mechanism can achieve the same preservation property.

**Potential construction:**

Revisions as row refinements. A revision narrows the row variable
by specifying tighter types for specific fields:

```kea
type HirExpr =
  Let { name: String, value: HirExpr, body: HirExpr }
  | ...

  @revision 2
  Let { name: Pattern, value: HirExpr, body: HirExpr }
  -- Pattern is a supertype of String
```

A function targeting revision 1 has the signature:

```kea
fn transform(expr: HirExpr { Let: { name: String | fr } | r })
    -> HirExpr { Let: { name: String | fr } | r }
```

A function targeting "revision 2 or later" has:

```kea
fn transform(expr: HirExpr { Let: { name: Pattern | fr } | r })
    -> HirExpr { Let: { name: Pattern | fr } | r }
```

The row variable `fr` absorbs new fields within `Let`. The row
variable `r` absorbs new nodes. The field type (`String` vs
`Pattern`) determines which revision the function handles.

**The gap:** This doesn't automatically generate the preservation
property. In José's system, writing `f(Schema) -> Schema`
automatically generates both arrows (r1 → r1 and r2 → r2). In
Kea, the function author would need to write the specific row
constraint manually, or the compiler would need a revision-aware
signature expansion — which is new inference machinery.

**Possible approaches:**

1. **Revision-aware signature expansion.** An annotation like
   `@revision_preserving` on a function causes the compiler to
   generate one arrow per revision, similar to José's automatic
   expansion. This is the most user-friendly but requires the
   most compiler work.

2. **GADTs as revision discriminants.** Encode the revision in a
   GADT parameter: `HirExpr R1` vs `HirExpr R2`. Functions
   polymorphic in the revision parameter (`HirExpr R where
   R: Revision`) preserve revision through parametric
   polymorphism. Less magic, but more verbose.

3. **Manual row constraints.** Library authors write explicit
   row constraints for each revision they support. No compiler
   magic, but high boilerplate and easy to get wrong.

4. **Hybrid: revision tags + row inference.** The compiler uses
   revision annotations to inform row inference, automatically
   tightening row variables when a revision is known. Less
   ambitious than full signature expansion, but captures the
   common case.

## What This Enables

### For StableHIR

Compiler passes and recipes that target StableHIR r1 continue to
work when r2 is released, even if r2 widens field types. The
revision preservation property guarantees that r1 inputs produce
r1 outputs. Recipe authors don't need to update for widening
changes — only for genuinely new patterns they want to handle.

### For library APIs

Any library shipping a public struct can use the same mechanism.
Widening a field type is a revision bump, not a breaking change.
Consumers on revision 1 keep working. Consumers that want the
wider type opt into revision 2. The type system enforces the
boundary.

### For the ecosystem

The cascading-breakage problem José describes — library A widens
a type, library B depends on A, library C depends on B, everything
breaks — is eliminated for widening changes. Only additive (rows)
and breaking (version bumps) changes remain. The space of
non-breaking evolution expands significantly.

## Semantic Invariants Are Still Not Covered

Revisions handle structural evolution (field types widen).
Validation passes handle semantic evolution (invariants change).
These are complementary, not substitutes.

A revision can't express "Let values must be in A-normal form."
That's a semantic invariant enforced by validation passes — pure
functions over IR that check properties the type system can't
encode. See COMPILER-AS-DATA.md § "IR evolution: structure and
semantics."

## Relationship to Other Briefs

- **ir-recipes-grammar-convergence** — defines StableHIR stability
  tiers. This brief extends the versioning story with revision
  preservation for field widening.
- **typed-grammar-interface** — grammars targeting StableHIR benefit
  from revision preservation. Grammar `check` methods that handle
  r1 nodes remain correct when r2 widens field types.
- **COMPILER-AS-DATA.md** — the "IR evolution" section references
  this brief as the design direction for revision-preserving
  evolution.

## Open Research Questions

1. **Can row polymorphism + revision annotations achieve the
   preservation property without intersection types?** The
   construction sketched above works for the common case (single
   field widening) but the interaction with multiple simultaneous
   widenings and nested types needs formal analysis.

2. **What's the inference cost?** José notes that each revisioned
   field adds one union to the type-checking workload per function.
   In a row-polymorphic system, the cost model may be different.
   Need to analyze whether revision-aware inference stays tractable.

3. **Should revisions be per-type or per-module?** Per-type is
   more granular but harder to reason about. Per-module is coarser
   but matches how semver works for packages. José's proposal is
   per-struct.

4. **How do revisions interact with the `From` trait?** If
   `Pattern` has `From String`, does that help with revision
   boundaries? Can the compiler use `From` instances to
   automatically bridge revisions?

5. **Is there prior art combining row polymorphism with revision
   preservation?** We haven't found any. This appears to be
   genuinely novel PL research. The closest work is José's
   set-theoretic approach, Rémy's original row typing, and the
   "Trees that Grow" extensible AST pattern. None combines rows
   with revision-preserving evolution.

## Recommendation

1. Capture this analysis now (this brief) so we don't paint
   ourselves into a corner.
2. Use version-tag-as-type-parameter as the v1 mechanism for
   StableHIR — coarse but correct.
3. Design revisions properly post-v1 when there's an actual
   ecosystem that needs the evolution guarantees.
4. If pursuing this, treat it as a research contribution — it's
   novel enough to be worth a paper.
