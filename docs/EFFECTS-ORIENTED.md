# Effects-Oriented Programming

## The problem

In most languages, a function signature tells you what goes in
and what comes out. It doesn't tell you what happens along the way.

```text
def fetch_user(id: int) -> User
```

Does this hit the network? Read a file? Mutate a cache? You can't
tell without reading the implementation. And the implementation can
change without the signature changing. A function that was pure last
week quietly starts doing I/O this week, and nothing in the type
system notices.

This matters because:

- **You can't trust function boundaries.** A "pure helper" that
  starts reading env vars breaks your test isolation, and you find
  out at runtime.
- **Refactoring is risky.** You rename a function, move some logic,
  and accidentally change what side effects happen where. The types
  still check. The tests still pass. The bug ships.
- **Testing requires ceremony.** You need mocks, DI containers, or
  monkeypatching to test code that does I/O — not because the test
  is complicated, but because the side effect is invisible.
- **Error handling is inconsistent.** Some functions throw, some
  return null, some return Result. Nothing enforces a policy across
  a codebase.
- **Concurrency is a minefield.** Nothing in a type signature tells
  you whether a function touches shared state, sends messages, or
  spawns threads.

Every production codebase eventually builds conventions around these
problems: "pure functions go in this module," "I/O only at the
boundary," "always return Result." But conventions are enforced by
code review. They erode.

## What if the compiler enforced them?

Kea tracks what functions *do*, not just what they return.

```kea
fn parse(_ text: String) -[Fail ConfigError]> Config
fn load(_ path: String) -[IO, Fail ConfigError]> Config
```

`parse` can fail but does nothing else. `load` reads the filesystem
and can fail. These aren't comments or conventions — they're checked
by the compiler. If `parse` starts reading files, it won't compile
until its signature says so.

The arrow tells you everything:

- `->` — pure. No side effects. Safe to memoise, reorder, parallelise.
- `-[IO]>` — performs I/O.
- `-[Fail E]>` — can fail with error type `E`.
- `-[IO, Fail E]>` — both.

The rest of this document explains the machinery that makes this
practical. But the core value is already here: you can read a
function signature and know what it does, and the compiler won't
let that contract drift.

---

## Effects are declared, not built in

An effect is a set of operations that a function might perform
but doesn't implement itself:

```kea
effect Log
  fn log(_ level: Level, _ msg: String) -> Unit

effect State S
  fn get() -> S
  fn put(_ new_state: S) -> Unit
```

Calling an effect operation adds that effect to the function's
signature. The compiler checks that the declared effects match
the body — you annotate them, and the compiler verifies:

```kea
fn process_order(order: Order) -[Log, State Stats]> Receipt
  Log.log(Info, "Processing order {order.id}")
  let stats = State.get()
  State.put(stats.with_order(order))
  order.to_receipt()
```

The programmer wrote `-[Log, State Stats]>` and the compiler
verified that the body performs exactly those effects — no more,
no less. And because effects are user-defined,
your domain gets its own vocabulary: `Audit`, `Metric`, `Cache`,
`Notify` — whatever your system actually does.

---

## Handlers give effects meaning

Declaring an effect says *what* a function does. A handler says
*how* it's done:

```kea
fn with_stdout_logger(f: () -[Log, e]> T) -[IO, e]> T
  handle f()
    Log.log(level, msg) ->
      IO.stdout("[{level}] {msg}")
      resume ()
```

This handler intercepts `Log` and implements it using `IO.stdout`.
The type tells the full story: `Log` goes in, `IO` comes out,
everything else (`e`) passes through. `resume ()` returns control
to where `Log.log` was called.

This separation — declaring what you need vs deciding how it's
provided — is what makes effects useful in practice. The business
logic says "I need logging." The infrastructure decides whether
that means stdout, a file, a network service, or nothing at all.
And the decision is explicit, scoped, and type-checked.

Handlers compose by nesting:

```kea
fn run_pipeline(order: Order) -[IO]> Receipt
  handle
    handle process_order(order)
      State.get() -> resume Stats.empty()
      State.put(s) -> resume ()
    Log.log(level, msg) ->
      IO.stdout("[{level}] {msg}")
      resume ()
```

Each handler peels off one effect. The final signature is `-[IO]>` —
the only thing left is the I/O the log handler introduces.

---

## Errors are an effect

Most languages treat errors as a special case — exceptions,
Result types, error codes — each with different propagation rules.
In Kea, failure is just another effect:

```kea
effect Fail E
  fn fail(_ error: E) -> Never

fn parse_port(s: String) -[Fail ConfigError]> Int
  let n = Int.parse(s)?
  if n < 1 or n > 65535
    Fail.fail(PortOutOfRange(n))
  else
    n
```

`?` propagates failures. `catch` converts a failure into a `Result`:

```kea
let result = catch parse_port("not_a_number")
-- result : Result(Int, ConfigError)
```

Because `Fail` is a regular effect, you get consistency for free.
Every function that can fail says so in its signature. Every error
type is tracked. You can't forget to handle an error — the
compiler knows whether `Fail` has been handled or is still
propagating.

---

## Pure functions are guaranteed pure

A function with `->` cannot perform effects. This isn't a
convention — it's a compiler guarantee:

```kea
fn total(items: List Item) -> Int
  items.map(|i| -> i.price * i.quantity).sum()
```

If someone adds a logging call inside `total`, the compiler
rejects it. This is the foundation everything else builds on:

- Pure functions can be tested with no setup — just call them.
- The compiler can safely reorder, memoise, or parallelise them.
- When you read `->` you *know* there's no hidden behaviour.
  Not because of a convention, but because it's checked.

In practice, this means your core business logic — the transforms,
validations, computations — stays pure. I/O and effects live at
the edges, in the functions that orchestrate the pure core. This
isn't a novel architecture pattern. What's novel is that the
compiler enforces it.

---

## Testing without mocks

The hardest part of testing in most languages is dealing with
side effects. You need mocks, stubs, DI containers, or
monkeypatching to intercept I/O. In Kea, you provide a different
handler:

```kea
test "config loading"
  let fake_files = Map.from([("/etc/app.toml", "[db]\nurl = ...")])

  let result = catch handle Config.load("/etc/app.toml")
    IO.read_file(path) ->
      resume(fake_files.get(path).unwrap_or(""))

  assert result == Ok(Config { db: DbConfig { url: "..." } })
```

The production code calls `IO.read_file` and can fail with
`Fail ConfigError`. The test intercepts `IO` with an in-memory
map and converts the `Fail` into a `Result` with `catch`. Same
code, same code path, different handler. No framework, no global
state, no cleanup. The handler is lexically scoped — it can't
leak into other tests.

This works because effects separate *what* from *how* at the
language level. The code under test declares that it needs
`IO.read_file`. It doesn't decide where the bytes come from.
That's the handler's job.

---

## Higher-order functions propagate effects

When a function takes a callback, the callback's effects flow
through automatically:

```kea
fn map(self: List A, f: A -[e]> B) -[e]> List B
```

If `f` is pure, `map` is pure. If `f` performs `IO`, `map`
performs `IO`. The effect variable `e` is inferred — you don't
annotate it at call sites:

```kea
-- pure: List(Int) -> List(Int)
numbers.map(|n| -> n * 2)

-- effectful: List(String) -[IO]> List(Bytes)
paths.map(|p| -> IO.read_file(p))
```

This matters because higher-order functions are everywhere.
Without effect propagation, wrapping a side-effecting function
in `map` would hide the effect. In Kea, it can't hide — the
type system carries it through.

---

## Effects are interfaces on computation

In most languages, if you want testable I/O, you define an
interface, inject it through constructors, wire up a DI container,
and create mock implementations. That's a lot of machinery to say
"this function reads files and I want to swap out the implementation."

Effects give you the same thing for free. A function's effect
signature *is* the interface:

```kea
fn process_config(path: String) -[IO, Fail ParseError]> Config
  let data = IO.read_file(path)
  Config.parse(data)?
```

No interface definition. No mock class. No DI container. No
constructor parameter. The caller provides the implementation
by wrapping the call in a handler:

```kea
-- Production: real IO, handled by the runtime
let config = process_config("app.toml")

-- Test: fake filesystem
handle process_config("app.toml")
  IO.read_file(path) -> resume "[db]\nurl = localhost"
```

The critical difference from traditional interfaces: effects
compose without wiring. If your function needs
`[IO, State Config, Log]`, you don't need a constructor that
takes three interface parameters and a factory that wires them
together. You just write the function. Each handler wraps at the
call site, they nest naturally, and the type checker ensures
nothing is unhandled.

---

## Effects and traits: two dimensions of polymorphism

Kea has both traits (ad-hoc polymorphism over types) and effects
(polymorphism over computation). Most languages give you one or
the other. Having both means you can abstract over *what a type
can do* and *what a function needs from its environment*
simultaneously.

Traits say "this type supports these operations":

```kea
trait Cacheable
  fn cache_key(self: Self) -> String
```

Effects say "this function needs these capabilities":

```kea
effect Cache K V
  fn lookup(key: K) -> Option V
  fn store(key: K, value: V) -> Unit
```

Together they express things neither can alone:

```kea
fn cached(key: K, compute: () -[e]> V) -[Cache K V, e]> V
  where K: Cacheable
  case Cache.lookup(key.cache_key())
    Some(v) -> v
    None ->
      let v = compute()
      Cache.store(key.cache_key(), v)
      v
```

The trait constrains which types can be cached. The effect
abstracts over how caching is implemented. In production, the
handler hits Redis. In tests, it's an in-memory map. In
benchmarks, it's a no-op that always misses. The function is
polymorphic in both dimensions at once.

This is also why Kea has no `Monad`, `Functor`, or monad
transformers. In Haskell, `MonadState`, `MonadReader`, `MonadIO`
are typeclasses that encode effects — and combining them requires
transformer stacks or mtl-style plumbing. In Kea, `State`,
`Reader`, `IO` are effects that compose by listing them in the
arrow: `-[State Int, Reader Config, IO]>`. No transformers, no
lifting, no `liftIO`. Traits handle polymorphism over types.
Effects handle polymorphism over computation. Each does its job.

---

## Records are structurally typed

Functions can require specific fields without requiring a
specific type:

```kea
fn greet(x: { name: String | r }) -> String
  "Hello, {x.name}"
```

This works with any record that has a `name: String` field.
No interface declaration, no inheritance. The `| r` means
"and whatever other fields you have."

---

## Where to start

Write pure functions with `->`. Move I/O to the edges.
Use `Fail` and `?` for errors. That's enough to get most
of the value.

Handlers, custom effects, and actor protocols are there when
you need them — but the first thing Kea gives you is the
ability to look at any function in your codebase and know
exactly what it does. Not what it might do. Not what it's
supposed to do. What the compiler has verified it does.
