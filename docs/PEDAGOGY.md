# Kea Pedagogy — The Compiler as Collaborator

*Governing document for all user-facing documentation, tutorials, error messages, REPL help text, and marketing copy.*

## Core Thesis

Kea's type system is powerful — algebraic effects, row polymorphism, GADTs, opaque types, typed actors. The documentation must never lead with that power. Instead, every feature is introduced through the problem it solves, not the theory it implements.

The governing metaphor: **the compiler is your collaborator.** You write Kea code to build things. The compiler reads your code and tells you what it knows: which functions are pure, where errors can occur, what messages an actor can receive, which operations might touch the network. It's not a gatekeeper — it's a second pair of eyes that never gets tired and never misses a case.

Programmers already want this. They write tests, linters, runtime assertions, defensive error handling. Those are all things the programmer does manually because the language can't help. Kea's type system handles them before the code runs.

## Principles

### 1. Problems first, theory never

Every type system feature is introduced by showing a bug it prevents or a guarantee it provides. The theoretical name appears only in a clearly-labelled appendix, if at all.

Bad: "Kea tracks algebraic effects via a row-polymorphic effect system."
Good: "The compiler knows which functions can touch the file system and which can't. It won't let you accidentally call a network function from inside a pure calculation."

Bad: "The `?` operator desugars `Fail E` via an implicit `Result` return."
Good: "`?` handles errors automatically. Each step either succeeds and continues, or short-circuits with the error. The compiler tracks which errors are possible and makes sure you've handled them all."

### 2. Category theory terms do not appear in user-facing documentation

Not in tutorials. Not in guides. Not in error messages. Not in API docs. They can appear in a clearly-labelled "Theory Deep Dive" appendix for the curious.

Kea has no `Monad` trait — effects replace monadic composition. But the concepts that monads describe in other languages are taught through their concrete Kea manifestations: error chaining with `?`, collection transformation with `.map`, optional handling with `match`. Users understand these by using them, not by learning category theory.

Absent from user-facing docs: monad, functor, applicative, endofunctor, morphism, catamorphism, natural transformation, Kleisli arrow. These words are for the appendix.

### 3. Terminology mapping

| Theory term | Kea user-facing term | Introduced as |
|---|---|---|
| Algebraic effects | "effect tracking" / "the compiler knows" | "the compiler knows this function talks to the network" |
| Row polymorphism | "flexible records" / "partial requirements" | "your function only requires the fields it uses" |
| Monad (other languages) | "effect handling" / "`?` for errors" | "effects replace monads — `?` handles errors, handlers handle effects" |
| Opaque type | "domain type" / "branded type" | "Revenue and Float are different things" |
| Effect polymorphism | "effect transparency" | "if your callback is pure, the whole pipeline is pure" |
| Kind | (invisible — never named) | (compiler internal) |
| Type constructor | (invisible — never named) | (compiler internal) |
| Unification | (invisible — never named) | (compiler internal) |
| Fail E | "error tracking" | "the compiler knows which errors this function can produce" |
| Actor / Ref | "service" / "process" | "a long-running service that receives messages" |

### 4. Error messages teach, not lecture

When the type system catches an error, the message explains the problem in domain terms and suggests a fix. It never requires type theory knowledge to understand.

Bad:
```
error: effect set {IO, Fail ParseError} is not a subset of {}
```

Good:
```
error: this function is marked pure, but it does I/O
  --> src/config.kea:12:5
   |
12 |   let data = File.read("config.toml")?
   |              ^^^^^^^^^ File.read requires IO
   |
   = help: either add IO to the function's effect signature:
           fn load_config(_ path: String) -[IO, Fail ParseError]> Config
           or pass the file contents as a parameter instead
```

Bad:
```
error: cannot unify Fail ParseError with Fail ConfigError
```

Good:
```
error: this function declares `Fail ConfigError`, but line 8
       produces a ParseError
  --> src/config.kea:8:20
   |
 8 |   let toml = Toml.parse(data)?
   |              ^^^^^^^^^^ this can fail with ParseError
   |
   = help: implement `From ParseError for ConfigError` to convert
           automatically, or use `catch` to handle ParseError
           explicitly before it propagates
```

### 5. Progressive disclosure through layers

Documentation is organised in concentric layers. Each layer introduces more power, motivated by increasingly sophisticated problems. A user can stop at any layer and be productive.

### 6. Entry points by background

Not everyone starts at Layer 1. The documentation should acknowledge three populations:

**From Python/TypeScript/Ruby:** Start at Layer 1. The type system is new. Emphasise that types are inferred — you rarely write them. Show how the compiler catches bugs you'd normally find in production. Effects (Layer 2) are the first "wow" moment.

**From Rust/Go/Java:** Start at Layer 2. They already know types and structs. Lead with what's different: effect tracking, row polymorphism, `Fail` as tracked errors rather than exceptions. Show how Kea gives them guarantees their current language doesn't.

**From Haskell/Scala/OCaml:** Start at the Theory Deep Dive appendix, then skim backwards. They'll recognise the type system features immediately and want to know the details. They'll appreciate that the user-facing docs don't require their background. Point them at the KERNEL spec.

Each entry point is a different path through the same material, not different material.

## The Five Layers

### Layer 1: Types as documentation

*Audience: Anyone. No programming background required.*
*Concept: Types are labels that describe what kind of data something is.*

```kea
let name = "Alice"          -- String
let age = 38                -- Int
let active = true           -- Bool
let score = 98.5            -- Float
```

Kea figures these out automatically. You rarely write them. When you see them in error messages, they're telling you what kind of data you have.

Structs group related data:

```kea
struct User
  name: String
  email: String
  active: Bool
```

Enums represent choices:

```kea
enum Status
  Active
  Inactive(reason: String)
```

Pattern matching handles every case:

```kea
match user.status
  Active -> "Welcome back"
  Inactive(reason) -> "Account inactive: {reason}"
```

If you add a new variant to `Status` later, the compiler finds every `match` that needs updating. No forgotten cases. No runtime surprises.

**Teaching point:** You already know types. "This is a number." "This is text." Kea writes it down for you and checks that you don't mix them up. `"hello" + 5` doesn't make sense — the compiler says so before you run the code.

**Teaching point:** `match` is like a `switch` that the compiler checks for completeness. Forget a case? The compiler tells you.

### Layer 2: Types as effects

*Audience: Anyone writing functions.*
*Concept: The compiler tracks what your functions do — not just what they return, but what they touch.*

This is Kea's distinctive feature. Every function has an effect signature that the compiler tracks automatically.

```kea
struct Config

  fn parse(_ text: String) -[Fail ConfigError]> Config
    -- can fail, but doesn't touch the file system or network

  fn load(_ path: String) -[IO, Fail ConfigError]> Config
    let text = File.read(path)?    -- IO: reads a file
    Config.parse(text)?            -- Fail: might fail to parse
```

The arrow tells you everything:
- `->` means pure. No side effects. Safe to memoise, reorder, test without mocks.
- `-[IO]>` means it touches the outside world. File system, network, clock.
- `-[Fail E]>` means it can fail with error type `E`.
- `-[IO, Fail E]>` means both.

You can combine them, and the compiler tracks the union automatically:

```kea
struct App

  fn run(_ config: Config) -[IO, Fail AppError]> Unit
    let db = Database.connect(config.db_url)?     -- IO + Fail DbError
    let users = db.query("SELECT * FROM users")?  -- IO + Fail QueryError
    for user in users
      Logger.info("Found: {user.name}")           -- IO
```

The compiler infers effects bottom-up. If you call a function with `IO`, your function has `IO`. If your callback is pure, a higher-order function stays pure:

```kea
struct Math

  fn double_all(_ xs: List Int) -> List Int
    xs.map(|x| -> x * 2)
    -- map's callback is pure, so double_all is pure
```

**Teaching point:** In most languages, any function might secretly read a file, hit the network, or throw an exception. You find out at 3am when production breaks. In Kea, the compiler tells you upfront. A function with `->` is *guaranteed* pure — you can trust it completely.

**Teaching point:** `?` is just "do this, and if it fails, stop." It replaces try/catch with something shorter that the compiler checks. You can't forget to handle an error — if a function can fail, its signature says so, and the caller must deal with it.

**Teaching point:** Effects are contagious in a good way. If you accidentally add a network call inside something that's supposed to be pure, the compiler catches it immediately — not after deployment.

### Layer 3: Types as contracts

*Audience: Anyone writing reusable functions or working on a team.*
*Concept: Function types are contracts — what goes in, what comes out, what could go wrong, and what the function touches.*

Row polymorphism lets functions work with any struct that has the fields they need:

```kea
struct Greeter

  fn greet(_ person: { name: String | r }) -> String
    "Hello, {person.name}!"
```

This works on any value with a `name: String` field. A `User`, an `Employee`, a `Customer` — it doesn't care about other fields. The `| r` means "and whatever else."

```kea
let user = User { name: "Alice", email: "alice@co.com", active: true }
let msg = Greeter.greet(user)   -- works: User has a name field
```

Combined with effects, function signatures become precise contracts:

```kea
struct Pipeline

  fn transform(_ input: { amount: Float | r }) -> { amount: Float | r }
    -- pure: no IO, no errors. Just transforms data.
    input~{ amount: Float.round(input.amount, 2) }

  fn load_and_transform(_ path: String) -[IO, Fail AppError]> List Transaction
    -- does IO (reads file), can fail (parse or IO errors)
    let raw = Csv.read(path)?
    raw.map(|r| -> Pipeline.transform(r))
```

Reading the signature tells you everything: `transform` is pure and total. `load_and_transform` does IO and might fail. No documentation required — the types *are* the documentation, and the compiler enforces them.

**Teaching point:** Type annotations on functions are the same as docstrings that say "takes X, returns Y, might fail with Z" — except the compiler enforces them. You can't lie in a type signature.

**Teaching point:** Row polymorphism means you write fewer functions. Instead of `greet_user`, `greet_employee`, `greet_customer` — you write `greet` once, for anything with a name.

### Layer 4: Types as capabilities

*Audience: Anyone building reusable libraries or complex systems.*
*Concept: Traits describe what a type can do. Your code can require capabilities without caring about specific types.*

```kea
trait Validatable
  fn validate(_ self: Self) -[Fail ValidationError]> Self
```

Any type can implement it:

```kea
impl Validatable for Transaction

  fn validate(_ self: Transaction) -[Fail ValidationError]> Transaction
    if self.amount < 0.0
      fail ValidationError.negative("amount", self.amount)
    if self.currency.is_empty()
      fail ValidationError.missing("currency")
    self
```

Now write generic functions over the capability:

```kea
struct Validation

  fn validate_all(_ xs: List A) -[Fail ValidationError]> List A where A: Validatable
    xs.map(|x| -> x.validate()?)
```

`validate_all` works on any list of `Validatable` things. Transactions, orders, user profiles — write it once.

Traits compose. A type can implement many traits. Generic code can require multiple capabilities:

```kea
struct Report

  fn summarise(_ items: List A) -> String where A: Show, A: Eq
    let unique = items.filter(|a| -> items.count(|b| -> a == b) == 1)
    unique.map(|a| -> a.show()).sort().join(", ")
```

**Teaching point:** Traits are "interfaces" or "protocols." They describe what a type can do, not what it is. Your function says "I need something Validatable" instead of "I need a Transaction."

### Layer 5: Types as invariants

*Audience: Anyone building systems where correctness matters.*
*Concept: The type system encodes domain rules that the compiler enforces everywhere.*

**Domain types:**

```kea
struct Revenue
  value: Float

  fn from_float(_ f: Float) -[Fail ValidationError]> Revenue
    if f < 0.0
      fail ValidationError.negative("revenue", f)
    Revenue { value: f }
```

`Revenue` is not a `Float`. You can't accidentally add revenue to a temperature, or mix currencies. The compiler prevents it everywhere.

**Pipeline stages (phantom types):**

```kea
struct Pipeline S
  data: List Record

struct Raw
struct Cleaned
struct Validated

struct Stages

  fn clean(_ p: Pipeline Raw) -[Fail CleanError]> Pipeline Cleaned
    -- ...

  fn validate(_ p: Pipeline Cleaned) -[Fail ValidationError]> Pipeline Validated
    -- ...
```

You can't validate a raw pipeline. You can't skip cleaning. The compiler rejects it. The stages are in the type — not in documentation, not in runtime checks. Combined with effects, the type tells the full story: `clean` can fail with `CleanError`, `validate` can fail with `ValidationError`, and neither does IO.

**Teaching point:** These are the same rules you'd write in a README: "always clean before validating," "never mix currencies." The difference is the compiler enforces them. A new team member, a late-night hotfix, a refactor six months later — the rules hold.

**Teaching point:** This is what "correctness by construction" means. Not "we tested it." Not "we documented it." The invalid state is *unrepresentable*. The wrong code doesn't compile.

## Layer 2+: Actors (taught separately, after effects)

Actors are introduced after Layer 2 because they build on effect tracking. They are not part of the core layer progression — they're a parallel track for concurrent systems.

```kea
struct Counter

  enum Msg
    Increment
    Decrement
    GetCount(Reply Int)

  fn init() -> Int
    0

  fn handle(_ state: Int, _ msg: Msg) -[Send]> Int
    match msg
      Increment -> state + 1
      Decrement -> state - 1
      GetCount(reply) ->
        reply <- state
        state
```

The type system enforces:
- Only `Counter.Msg` values can be sent to a `Ref Counter.Msg`.
- The `handle` function has `Send` effect (it can reply to messages) but no `IO` — it doesn't touch the file system or network.
- Sending a wrong message type is a compile error, not a runtime crash.

**Teaching point:** An actor is a long-running service that receives typed messages. Think of it like a server endpoint, but the compiler checks that you're sending the right request type.

## The "Theory Deep Dive" Appendix

A clearly-labelled separate document for the curious. Not linked from tutorials or getting-started guides. Contains:

- The formal names: algebraic effects, row polymorphism, GADTs
- How they relate to Haskell, OCaml, Scala, Rust equivalents
- How `?` desugars through `Fail` and `Result`
- Effect set algebra and join rules
- Why Kea doesn't need HKTs (effects replace monadic composition)
- Category theory connections (for those who want them)
- Academic references

This appendix exists for library authors, language contributors, and the theoretically curious. It is never required reading.

Trait documentation should include brief notes at the bottom for those who know what they're looking for. For example, the `Fail` effect doc could note: "If you're coming from Haskell, `Fail` replaces the `MonadError` pattern. See deep-dive/type-theory.md." This line is invisible to application developers — it's at the bottom of the doc — but findable by someone who already knows the concept.

## Documentation structure

```
docs/
  getting-started/
    first-steps.md           # Layer 1 only
    your-first-project.md    # Layers 1-2
    functions-and-effects.md # Layer 2, the hook
  guides/
    error-handling.md        # Fail/Result/? without theory
    building-services.md     # Layers 2-3, web/CLI examples
    reusable-components.md   # Layer 4, traits as capabilities
    domain-modelling.md      # Layer 5, opaque types + phantom types
    actors.md                # Typed actors, practical focus
    testing.md               # Pure functions are trivially testable
  reference/
    types.md                 # All types, practical descriptions
    traits.md                # All traits, what they enable
    effects.md               # Effect system, practical reference
    error-catalog.md         # Every error message with examples
    stdlib.md                # Standard library reference
  deep-dive/
    type-theory.md           # The appendix — formal names, theory
    effect-system.md         # Algebraic effects internals
    type-system-internals.md # How inference works, for contributors
    comparison.md            # Kea vs Haskell/Scala/Rust type systems
  PEDAGOGY.md                # This document
  KERNEL.md                  # Language specification
```

## Errors as first-class citizens

Errors are a product, not a byproduct. Every error the compiler can produce has a stable code (E0001, E0002, ...), a structured `Diagnostic` type with machine-readable fields, and a human-readable rendering with source context. This is load-bearing for two reasons:

1. **MCP agents consume diagnostics programmatically.** The MCP server returns structured JSON — category, code, location, labels, help. An agent can pattern-match on `E0001` (TypeMismatch) and know what to do. Error codes are stable API: they don't change between releases.

2. **Humans see ariadne-rendered output.** The same `Diagnostic` struct renders to colored terminal output with source snippets, underlines, and fix suggestions. No information is lost — the human sees everything the machine sees, just rendered differently.

The `Diagnostic` type is the single source of truth. Two consumers, two renderers, one structured type. This means:

- **Every diagnostic is testable.** We can assert on category, code, labels, help text in unit tests.
- **Every diagnostic is documentable.** Each error code gets a reference page: what it means, common causes, examples, fixes (see `reference/error-catalog.md` in the doc structure below).
- **Agents improve with the compiler.** As we add better help text and fix suggestions, both humans and agents benefit simultaneously.

### Context-aware messages

The type checker's constraint system carries `Provenance` — where each type expectation came from (function argument, return position, if condition, match arm, let binding). This means error messages explain *why* in domain terms:

- "argument 2 has type String but `count_to` expects Int" (not "cannot unify String with Int")
- "if condition must be Bool, but this expression has type Int" (not "expected Bool, got Int")
- "`Toml.parse` can fail with ParseError, but this function doesn't declare any errors" (not "Fail ParseError not in effect set")

The `Reason` enum is the mechanism. Every constraint records *why* it was created, so when it fails, the error message tells the story.

## Error message guidelines

### Always include

1. **What went wrong** — in domain terms, not type theory terms
2. **Where** — point at the exact expression
3. **Why** — what rule was violated, what effect or type was expected
4. **How to fix it** — concrete suggestion with code

### Never include

1. Internal type variable names in user-facing text (say "this value" not "t42")
2. Kind annotations (say "`.map` works on container types like List, Option, and Result" not "expected kind * -> *")
3. Unification failure details (say "expected String, got Int" not "cannot unify String with Int")
4. Theory terminology (say "this function can fail" not "Fail effect in the effect row")

### Effect-specific error guidance

Effect errors should always explain *what the function does* that requires the effect, not *what effect is missing*:

Bad: "effect set mismatch: {IO} ⊄ {}"
Good: "this function is pure, but `File.read` on line 12 accesses the file system"

Bad: "Fail ParseError not in declared effects"
Good: "`Toml.parse` can fail with ParseError, but this function's signature doesn't declare any errors"

### Exception: library authors

When writing code that defines traits or uses effect-parameterised types, users may encounter kind errors or trait resolution failures. These messages can use slightly more technical language, but should still lead with the problem:

```
error: `Server Int` uses Int as an effect set, but Int is a type
  --> src/lib.kea:10:1
   |
10 | let s: Server Int = ...
   |               ^^^ Int is a type, not an effect set
   |
   = help: Server expects an effect set like [IO, Fail AppError].
           Try: Server [IO, Fail AppError]
   = note: (for library authors) Server's parameter has kind Eff.
           Int has kind *.
```

The `note:` line provides the technical detail for those who want it. The main message is understandable without it.

## Voice and tone

- **Warm, not condescending.** Assume the reader is intelligent and busy. Don't over-explain things they know. Don't assume they know type theory.
- **Concrete, not abstract.** Every explanation includes a code example that does something real. No `foo`/`bar` — use realistic data: configurations, API responses, transactions, user records.
- **Confident, not apologetic.** Don't say "Kea's effect system might seem unusual but..." Say "Kea tracks side effects at compile time. Here's how."
- **Honest about trade-offs.** If an effect annotation is verbose, say so. If a pattern is unfamiliar, acknowledge it and show the payoff. Don't pretend everything is simple — show that the complexity exists for a reason.
- **Effects are the hook, not the barrier.** Layer 2 should feel like a superpower, not a chore. The first time a programmer sees the compiler catch an accidental IO call inside a pure function, they should think "where has this been all my life?" — not "this is a lot of ceremony."

## What success looks like

A TypeScript developer picks up Kea. After the getting-started guide (Layers 1-2), they're writing functions with compile-time effect tracking. They never encounter the word "monad." They understand `?` as "handle errors automatically." They think of effects as "what the compiler knows about my code." They think of traits as "what this type can do." If they later want to understand why `.map` works uniformly across Option, Result, and List, the deep-dive appendix is there. But they never need it.

A Rust programmer picks up Kea. They start at Layer 2, recognise the type system from Rust's, and immediately appreciate effect tracking — something Rust doesn't have. They see `-> ` vs `-[IO]>` and understand the value instantly. They're productive in hours.

A Haskell programmer picks up Kea. They find the deep-dive appendix, see the formal connections, and recognise the prelude traits. They appreciate that the user-facing documentation doesn't require their background — it means their teammates can use the same language. They read the KERNEL spec and feel at home.

All three are productive. None feels talked down to. That's the goal.

## On naming: Kea

The name comes from the kea, a parrot endemic to the Southern Alps of New Zealand. Kea are known for their intelligence, curiosity, and problem-solving ability in harsh environments. The name is a Māori word — an onomatopoeia for the bird's call. The kea is considered taonga (treasure) by Māori and was regarded as kaitiaki (guardians) by the Waitaha.

We use the name with respect for its origins. If this project becomes public-facing, we will consult with Māori cultural advisors and acknowledge the name's origin in project materials. We will not use Māori visual culture (koru patterns, tā moko, etc.) in branding or design.
