# Kea: The Vision

**Kea is an effect-driven language where the struct is the universal
unit of organization and the handler is the universal unit of
composition.**

Everything — modules, actors, supervisors, applications — is a
struct. Everything interesting a program does — IO, state, messaging,
allocation — is an effect. The type system tracks both using the
same mechanism: Rémy row polymorphism. This document explains why
we think that combination produces something genuinely new.

---

## The Structural Claim

Most languages have two type systems: one for data, one for behavior.
The data system tracks what values are (Int, String, User). The
behavior system — if it exists at all — is ad hoc: checked
exceptions in Java, `async` coloring in Rust, monad stacks in
Haskell. These are bolted-on mechanisms trying to answer the
question the data type system answers naturally: "what am I
dealing with here?"

Kea's claim is that data and effects are the same kind of thing
— **rows** — and should use the same polymorphism mechanism.

A record row: `{ name: String, age: Int | r }` — a value with
at least these fields, possibly more.

An effect row: `-[IO, Fail E | e]>` — a computation with at
least these effects, possibly more.

One unification algorithm handles both. The same `| r` that makes
a function work with any record that has a `name` field also makes
a function work with any effect set that includes `IO`. Adding a
field to a record and adding an effect to a computation are the
same type-level operation.

This is the foundation everything else builds on. Row polymorphism
makes effects compose like data composes: naturally, without
boilerplate, without transformer stacks, without explicit plumbing.
When `f` needs `[IO, State S]` and `g` needs `[IO, Log]`, calling
both needs `[IO, State S, Log]`. The rows merge. That's it.

On top of this foundation, one organizational primitive — the
struct — serves every role. A module is a singleton struct.
An actor is a struct that implements the `Actor` trait. A
supervisor is a struct that manages child actors. Your
application's `Main` is a struct. The traits a struct implements
determine its role in the system.

The result: there is one kind of polymorphism (rows), one kind
of organizational unit (struct), and one kind of composition
point (handler). The language is small. What emerges from the
combination is not.

---

## Five Pillars

Five features that reinforce each other. Each exists in other
languages. The combination — and the fact that they share the
row polymorphism substrate — is what we think is new.

### 1. Algebraic Effects

Effects are user-defined, first-class, and tracked in the type:

```kea
effect Log
  fn log(_ level: Level, _ msg: String) -> ()

effect Tx
  fn query(_ sql: String) -> Rows
  fn execute(_ sql: String) -> Int

struct Orders
  fn process(_ order: Order) -[Log, Tx, Fail OrderError]> Receipt
    Log.log(Info, "Processing order {order.id}")
    let items = Tx.query("SELECT * FROM items WHERE order_id = {order.id}")
    if items.is_empty()
      fail OrderError.NoItems
    -- ...
```

The signature `-[Log, Tx, Fail OrderError]>` is the full story.
This function logs, uses a database transaction, and may fail
with an `OrderError`. Nothing else.

Handlers give effects meaning and remove them from the type:

```kea
struct Logging
  fn with_stdout(_ f: () -[Log, e]> T) -[IO, e]> T
    handle f()
      Log.log(level, msg) ->
        IO.stdout("[{level}] {msg}")
        resume ()
```

The handler removes `Log` and adds `IO`. For testing, a different
handler removes `Log` and adds nothing:

```kea
struct Logging
  fn with_capture(_ f: () -[Log, e]> T) -[e]> (T, List String)
    let logs = []
    let result = handle f()
      Log.log(level, msg) ->
        logs = logs ++ [msg]
        resume ()
    (result, logs)
```

Same code under test. Different handler. No mocking framework,
no dependency injection container. Just a function that intercepts
an effect and does something else with it.

### 2. Rémy Row Polymorphism

Row polymorphism is what makes effects practical rather than
academic. Without it, effect signatures become a bookkeeping
chore. With it, you write what you care about and the rest
flows through.

```kea
struct List
  fn map(_ self: List A, _ f: A -[e]> B) -[e]> List B
```

The effect variable `e` represents any set of effects. Pass a
pure function, `map` is pure. Pass a function with `[IO, Log]`,
`map` has `[IO, Log]`. The polymorphism is automatic.

The same mechanism handles data:

```kea
struct Greeter
  fn greet(_ person: { name: String | r }) -> String
    "Hello, {person.name}!"
```

Any value with a `name: String` field fits — `User`, `Company`,
`#{ name: "World" }`. One unification algorithm. Records and
effects are both rows.

When the compiler unifies `{ x: Int | r1 }` with `{ y: Bool | r2 }`:

```
r1 ~ { y: Bool | r3 }
r2 ~ { x: Int  | r3 }
r3 lacks x, y
```

Rémy-style decomposition. Lacks constraints propagate during
unification. Rows merge naturally.

The consequence for effects: composing two effectful computations
is set union on their effect rows. No monad transformers. No
explicit lift. No restructuring when you add an effect. The type
system handles composition the same way it handles adding a field
to a record.

### 3. Universal Method Syntax

When you type `value.` in Kea, you see the full behavioral
surface of that value:

- **Fields** — what data it holds
- **Inherent methods** — defined in the struct block
- **Trait methods** — from in-scope traits implemented for its type
- **Qualified functions** — any function where it can slot in
  as receiver, via `value.Module::function()`

For each one, the effect signature says what happens when you
call it. `value.save()` shows `-[DB, Log]>`. `value.validate()`
shows `->` — pure. The dot is a window into the effect
landscape.

Four call forms cover every case (see CALL-SYNTAX.md):

```kea
users.filter(|u| -> u.active)             -- method call (~90%)
Point.origin()                             -- prefix call (~8%)
widget.Drawable::render()                  -- qualified dispatch (~1%)
text.String::replace("old", $, "new")     -- receiver placement (~1%)
```

No pipe operator. The dot and `$` handle everything pipes would,
with the effect signature visible at every step of the chain:

```kea
users
  .filter(|u| -> u.active)
  .map(|u| -> u.name)
  .sort()
  .take(10)
```

### 4. Struct-Everything

No bare functions. Every function belongs to a struct. Structs
are the only organizational unit.

**Modules are singleton structs:**

```kea
struct Math
  fn clamp(_ value: Float, min: Float, max: Float) -> Float
    if value < min then min
    else if value > max then max
    else value
```

**Actors are structs with an `Actor` trait implementation:**

```kea
struct Counter
  count: Int

Counter as Actor
  type Msg = CounterMsg
  type Config = Int

  fn init(_ config: Int) -> Counter
    Counter { count: config }

  fn handle(_ self: Counter, _ msg: CounterMsg T) -[Send]> (Counter, T)
    match msg
      Increment -> (self~{ count: self.count + 1 }, ())
      Decrement -> (self~{ count: self.count - 1 }, ())
      Get       -> (self, self.count)
```

**Main is a struct. It could also be a supervisor:**

The KERNEL defines the `Actor` trait (§19.3) and sketches
supervision (§19.5) with opaque `ChildId` handles and restart
strategies. The exact `Supervisor` trait is a library design
question — but the shape is clear: a struct that declares its
children, their configurations, and a restart strategy. Main
can be that struct. Your application's entry point IS its
supervision root.

```kea
-- Proposed — not yet in KERNEL. The supervision trait API is
-- a library design decision for kea-actors.
struct Main
  fn main() -[IO, Spawn]>
    -- start supervision tree, then run application logic
    ...
```

**Why this matters:**

- Dependency injection is struct substitution. Your `Database`
  module is a singleton struct. In tests, `MockDatabase` is
  another singleton struct implementing the same trait. No
  container, no reflection.

- Capabilities emerge from effects. A module's methods declare
  their effects. Calling those methods requires a handler in
  scope. The struct boundary is the capability boundary.

- The dot works the same everywhere — modules, actors, data
  values. One dispatch mechanism.

### 5. GADTs

GADTs encode invariants in types. They make the actor story
type-safe.

**GADTs type actor protocols:**

```kea
enum CounterMsg T
  Increment   : CounterMsg ()
  Decrement   : CounterMsg ()
  Get         : CounterMsg Int
```

The GADT parameter `T` encodes the response type.
`Send.ask(ref, Get)` returns `Int` — not `Any`, not a runtime
cast. `Send.tell(ref, Increment)` compiles because
`Increment : CounterMsg ()` — you can't silently discard a
response from a message that expects one.

---

## Typed Actors

Erlang's OTP is the gold standard for reliable concurrent
systems. Kea aims to bring its model into a statically typed
world. This is ambitious and partly aspirational — the `Actor`
trait is specified (KERNEL §19.3), but supervision and registry
APIs are library design work that hasn't been fully done yet.

### What the KERNEL specifies

The actor library defines two effects:

```kea
effect Send
  fn tell(_ ref: Ref M, _ msg: M ()) -> ()
  fn ask(_ ref: Ref M, _ msg: M T) -> T

effect Spawn
  fn spawn(_ actor: A, _ config: A.Config) -> Ref A.Msg where A: Actor
```

`Send` and `Spawn` are ordinary effects. They're handled by the
actor runtime in production. In tests, they're handled by mock
handlers — same mechanism as any other effect.

`Ref M` is an opaque handle to an actor accepting protocol `M`.
The GADT parameter means `ask` returns the type encoded in the
message. This is the type-safety that Erlang lacks and that
Akka achieves only partially.

### What we think supervision looks like

The KERNEL defines supervision loosely: opaque `ChildId` handles,
restart strategies (OneForOne, OneForAll, RestForOne), restart
intensity. The exact trait API is a library design question.

The structural claim: since everything is a struct, and actors
are structs implementing `Actor`, supervisors should be structs
implementing a supervision trait. Main can be such a struct. The
supervision tree is struct composition — data the compiler can
see, not runtime configuration.

The OTP mapping we're targeting:

| OTP concept | Kea equivalent |
|---|---|
| `module` | Singleton struct |
| `gen_server` | Struct implementing `Actor` (KERNEL §19.3) |
| `gen_statem` | Struct implementing `Actor` + `State S` effect |
| Message passing | `Send` effect, typed via GADTs |
| Process dictionary | `State S` effect, scoped by handler |
| `supervisor` | Struct implementing supervision trait (proposed) |
| `application` | `Main` struct (proposed) |
| Fault tolerance | Runtime isolation + effect scoping (see below) |

### On fault boundaries

In Erlang, crash isolation comes from the BEAM's process model:
separate heaps, separate stacks, no shared mutable state. A
process crash cannot corrupt another process.

In Kea, the picture is layered:

- **Effect scoping provides logical isolation.** Each actor's
  `State S` effect is scoped to its handler. One actor's state
  cannot leak into another's. When a supervisor restarts an actor,
  it calls `init` with fresh state. The type system verifies that
  `handle` returns `(Self, T)` — the actor always produces its
  next state explicitly.

- **The runtime provides physical isolation.** Crash recovery
  (catching panics, restarting actors) is a runtime concern, not
  something the type system proves. Effects scope state and
  behavior; the runtime provides the safety net when things go
  wrong despite the types.

This is weaker than Erlang's guarantee (separate heaps) but
stronger than most typed actor systems (which don't track effects
at all). The honest claim: effects make actor state management
*correct by construction*, and the runtime makes crash recovery
*possible*. Together, they approximate OTP's reliability model
in a statically typed language.

---

## What Emerges

A few things fall out of the combination that we didn't set
out to design individually.

### Testing without infrastructure

Every effect has a test handler. Handlers compose by nesting.
Test setup is function calls, not framework configuration:

```kea
struct OrdersTest
  fn test_processing() -[Fail TestError]>
    let (result, logs) = Logging.with_capture(|| ->
      MockDb.with_test_data(test_data, || ->
        Orders.process(test_order)
      )
    )
    assert result == Ok(expected_receipt)
    assert logs.any(|l| -> l.contains("Processing order"))
```

`Orders.process` has effects `[Log, Tx, Fail OrderError]`.
Each effect gets a test handler. The code under test doesn't
know and doesn't change.

### Capabilities without a framework

Effects are capabilities. A handler determines what's permitted:

```kea
struct Sandbox
  fn run(_ plugin: Plugin, _ allowed_paths: Set String) -[Log]>
    handle plugin.execute()
      IO.read_file(path) ->
        if allowed_paths.contains(path)
          resume IO.read_file(path)
        else
          fail PermissionDenied(path)
      IO.net_connect(_, _) ->
        fail PermissionDenied("network access")
```

The handler intercepts `IO` and restricts it. The plugin doesn't
know it's sandboxed. This isn't a security primitive — it's a
consequence of effects being the only way to do things.

### Refactoring is compiler-guided

When you add an effect to a function, the compiler shows you
every call site that needs a handler. When you remove one, it
shows you every handler that's now dead code. Effect signatures
are machine-checked documentation that stays current because the
compiler enforces them.

### The REPL explores effects

In an effect-driven language, the REPL tracks what effects the
session has performed. `:effects` shows the current effect set.
`:type expr` shows the full effect signature, not just the return
type. Swapping handlers interactively lets you explore what a
library does by watching its effects. See REPL.md for the full
design.

---

## Where Kea Sits

No new language exists in a vacuum. Here's how we think about
the relationship to the languages that most influenced the design.

**Rust** gave us `Unique` types, the idea that ownership can
be tracked statically, and Cranelift. Kea's memory model
(refcounting, copy-on-write, `Unique T` for hot paths, arenas
via the `Alloc` effect) trades Rust's fine-grained borrow
checker for simpler code and relies on effects to track what
Rust tracks with lifetimes. Kea is an application language;
Rust is where you write the runtime underneath it.

**Haskell** gave us GADTs, type inference, and the understanding
that tracking effects in the type system matters. Kea replaces
monad transformers with row-polymorphic effects, which compose
better and require less expertise to use. Kea doesn't need HKTs
because effects replace monadic composition — the primary
motivation for `* -> *` disappears. The indentation-sensitive
syntax is closer to Haskell than to anything else.

**Erlang/OTP** gave us the actor model, supervision trees, and
"let it crash." Kea's contribution is bringing those ideas into
a statically typed world where message protocols are checked at
compile time. Whether we actually achieve OTP's reliability
properties depends on the runtime, not just the types — that's
ongoing work.

**Koka** pioneered practical algebraic effects with row-based
effect typing. Kea extends the idea with GADTs (for typed actor
protocols) and the struct-everything organization. Koka showed
effects could work; Kea is trying to build a full language
around them.

**OCaml 5** added algebraic effects to a mature ecosystem. OCaml's
effects are untyped at the language level (the effect type is not
tracked in function signatures). Kea's effects are fully typed
and use row polymorphism. Different tradeoff: OCaml gets ecosystem
compatibility; Kea gets static effect tracking.

The unique position, as far as we can tell: no existing language
combines row-polymorphic effects, GADTs, typed actors, and
struct-everything modules where all of these share the same
polymorphism substrate. Koka comes closest for effects. Haskell
comes closest for the type system. Erlang comes closest for
actors. We're trying to make them work as one thing rather than
five separate features.

---

## What the Design Enables

The combination of typed effects, row polymorphism, and actors
opens compilation strategies that aren't available to languages
where these features are bolted on.

**JS codegen and automatic client/server partitioning.** A second
codegen backend (alongside Cranelift) can target JavaScript. The
effect system determines the partition: `->` functions are pure
and can run anywhere. `-[DB, IO]>` functions can only run on the
server. `-[DOM, State S]>` functions can only run on the client.
A `Server` effect marks the RPC boundary — `Server.fetch(get_users)`
compiles to an HTTP endpoint on the server and a fetch call on the
client, with the serialisation boundary type-checked end-to-end.

This is the architecture of Next.js server actions and Leptos
server functions, but the compiler determines the split from
effect signatures rather than manual string directives or macro
annotations. The type system guarantees the serialisation boundary
is sound.

**Effect-driven reactive compilation.** Row polymorphism gives
the compiler field-level dependency information. Effect arrows
give it purity proofs. Together, the compiler can generate
Svelte-style fine-grained DOM updates without special reactive
syntax — the information Svelte extracts from `$state` rune
analysis, Kea already has from the type and effect system. Pure
components (`->`) never re-render when inputs haven't changed,
proven by the compiler rather than manually memoized by the
developer.

**Row-polymorphic templates.** `html {}` blocks where field
references are type-checked against the input row type. A
template using `{person.name}` and `{person.age}` accepts any
record with those fields — structural subtyping on props. No
`interface Props` declarations. Misspelled fields are compile
errors.

These are Phase 2+ targets, not v0 work. But the language
design decisions being made now — effects as the organizing
principle, row polymorphism on both records and effects, no
HKTs — are what make them possible. The web framework isn't a
library sitting on top of the language. It's what falls out when
you point the language at the browser.

---

## Design Principles

**Effects are the organizing principle.** Every design decision
is evaluated through: does this make effects more useful, more
composable, more visible? Effects aren't a feature of Kea. Kea
is a language designed around effects.

**The struct is the universal unit.** No class hierarchy, no
separate module system, no actor primitives. Structs with traits.
The traits determine what a struct is — a module, an actor, a
supervisor. One mechanism, many roles.

**The handler is the universal seam.** Where you configure
behavior, where you test, where you sandbox, where you intercept.
Every handler boundary is a composition point and a potential
isolation boundary.

**Progressive disclosure.** Effects are inferred — you don't
need to annotate them until you want to. Row polymorphism works
invisibly. Actors are a library you import when you need
concurrency. Each feature reveals itself when you need it.

**The type system serves the programmer.** Types catch mistakes,
guide refactoring, document intent. Error messages explain
problems in plain language, never expose unification variables,
and suggest fixes. If the type system is a puzzle to satisfy,
the design is wrong.

---

*Kea: clever, small, unexpectedly powerful.*
