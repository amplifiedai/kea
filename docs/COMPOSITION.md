# Values, Composition, and Why OOP Is Wrong

Kea has no classes, no inheritance, no mutable objects. This is
not a limitation — it's the point. Kea's model is fundamentally
different from object-oriented programming, and it's better in
ways that matter for real software.

This document explains the model, why it works, and what you
gain from it.

---

## The Model: Values In, Values Out

In Kea, everything is a value. Structs are values. Records are
values. Lists are values. Functions transform values into new
values. That's the whole model.

```kea
let user = { name: "Alice", age: 30, role: "admin" }
let updated = user~{ age: 31 }
-- user is unchanged. updated is a new value.
```

Methods on structs are the same — they take a value (the receiver)
and return a new value:

```kea
struct User
  name: String
  age: Int

  fn with_name(_ self: User, _ name: String) -> User
    self~{ name: name }

  fn with_age(_ self: User, _ age: Int) -> User
    self~{ age: age }

  fn validate(_ self: User) -[Fail ValidationError]> User
    if self.name.is_empty()
      fail ValidationError("name is required")
    if self.age < 0
      fail ValidationError("age must be non-negative")
    self
```

These are **combinators** — composable functions from value to
value. They chain naturally:

```kea
let valid_user = User.default()
  .with_name("Alice")
  .with_age(30)
  .validate()
```

Each step takes a value and produces a new one. The chain is a
pipeline of transformations. Effects (like `Fail`) are tracked
at each step — the type signature tells you exactly which step
can fail.

---

## Why This Is Better Than Mutable Objects

### Problem 1: Partial Mutation

In OOP, methods mutate the object in place. If step 3 of 5
throws an exception, the object is half-mutated:

```java
// Java — what state is user in after an exception?
user.setName("Alice");
user.setAge(30);
user.validate();        // throws — but name and age already changed
user.setRole("admin");  // never runs
user.save();            // never runs
// user is now { name: "Alice", age: 30, role: null }
// half-constructed, possibly invalid
```

In Kea, each step produces a new value. If `validate()` fails,
you still have the original value — nothing was mutated:

```kea
-- Kea — failure doesn't corrupt anything
let result = catch(|| ->
  User.default()
    .with_name("Alice")
    .with_age(30)
    .validate()          -- fails here
    .with_role("admin")  -- never runs
    .save()              -- never runs
)
-- User.default() is untouched. result is Err(ValidationError(...))
```

### Problem 2: Shared Mutable State

In OOP, two references to the same object see each other's
mutations. This is the root cause of most concurrency bugs and
many single-threaded bugs:

```python
# Python — spooky action at a distance
admin_user = get_user("alice")
display_user = admin_user  # same object!
display_user.role = "viewer"  # "for display only"
admin_user.save()  # oops — saved with role "viewer"
```

In Kea, values are immutable. Two bindings to the same value
cannot interfere:

```kea
let admin_user = User.get("alice")
let display_user = admin_user~{ role: "viewer" }
admin_user.save()  -- saves with original role
```

### Problem 3: Inheritance Fragility

OOP organises behavior through class hierarchies. Adding a method
to a base class can break subclasses. Overriding a method changes
behavior for all callers. The "fragile base class problem" is
well-studied and never solved — only mitigated by conventions.

Kea has no inheritance. Behavior is organised through traits:

```kea
trait Validate
  fn validate(_ self: Self) -[Fail ValidationError]> Self

trait Persist
  fn save(_ self: Self) -[IO, Fail DbError]> Self
```

A struct implements whichever traits it needs. There's no hierarchy
to be fragile. Adding a method to a trait doesn't affect structs
that don't implement it.

### Problem 4: Dependency Injection Ceremony

OOP testing requires mock objects, DI containers, and interface
abstractions to replace dependencies:

```java
// Java — DI ceremony for testability
class OrderService {
    private final PaymentGateway gateway;
    private final Logger logger;

    @Inject
    OrderService(PaymentGateway gateway, Logger logger) {
        this.gateway = gateway;
        this.logger = logger;
    }
}

// test
OrderService svc = new OrderService(mockGateway, mockLogger);
```

In Kea, dependencies are effects. Testing swaps the handler:

```kea
-- production code — no DI needed
struct Orders
  fn process(_ order: Order) -[IO, Log, Fail PaymentError]> Receipt
    Log.info("Processing order " ++ order.id)
    let charge = IO.post(payment_url, order.total)
    Receipt.from(order, charge)

-- test — swap the handler, not the code
test "order processing"
  let (receipt, logs) = handle Orders.process(test_order)
    Log.info(msg) -> resume ()       -- swallow logs
    IO.post(url, body) ->
      resume test_charge_response    -- mock HTTP
  check receipt.total == test_order.total
```

No interfaces. No mocks. No DI container. The effect system IS
the dependency injection mechanism, and the compiler verifies
that every effect is handled.

---

## Copy-on-Write: Immutability at Mutation Speed

The obvious objection: "immutable values means copying
everything, which is slow."

No. Kea uses reference counting with copy-on-write (CoW). The
semantics are always immutable, but the runtime mutates in place
when it's safe:

```kea
let user = User.new("Alice", 30)
let updated = user~{ age: 31 }
```

What happens at runtime:

1. Check the reference count of `user`.
2. If refcount == 1 (nobody else references it): **update in
   place**. No copy. No allocation. Same speed as mutation.
3. If refcount > 1 (shared): copy, then update the copy.

The programmer writes immutable code. The runtime executes
mutable code when it can prove it's safe. The semantics never
change — only the performance.

### Unique T: Guaranteed In-Place

When performance matters and you need to guarantee no copying,
use `Unique T`:

```kea
fn build_large_buffer() -> Unique Buffer
  let buf = Unique Buffer.new(1_000_000)
  -- every update is unconditionally in-place
  -- the compiler proves buf has exactly one owner
  buf~{ data: fill(buf.data, 0) }
```

`Unique T` tells the compiler: this value has one owner. The
compiler enforces it (use-after-move is a compile error) and
rewards you: functional updates skip the refcount check entirely.
Unconditional in-place mutation.

You get the programming model of immutability — each step is a
new value, composition is safe, reasoning is local — with the
performance of C-style mutation.

---

## Combinators Compose, Mutation Doesn't

The deepest advantage of value-returning methods is
**composability**. Functions from values to values compose.
Mutations don't.

### Composition is associative

```kea
-- these are equivalent
user.with_name("Alice").with_age(30)
user.with_age(30).with_name("Alice")
```

Order doesn't matter (for independent fields). You can reorder,
factor out, and recombine freely. Mutable setters can't promise
this — `setName` might have side effects that depend on the
current state.

### Combinators are testable in isolation

Each combinator is a pure function. Test it alone:

```kea
test "with_age updates age"
  let user = User.new("Alice", 30)
  check user.with_age(31).age == 31
  check user.age == 30  -- original unchanged
```

No setup. No teardown. No mock state. The function takes a value
and returns a value.

### Combinators enable replay and branching

Because each step produces a new value, you can keep intermediates
and branch from any point:

```kea
let base = Config.default()
  .with_host("localhost")
  .with_port(8080)

let dev = base~{ debug: true, log_level: "trace" }
let prod = base~{ debug: false, log_level: "error" }
-- both share the base, diverge from it
```

With mutable objects, you'd need to clone before branching —
and hope nobody mutates the clone.

### Effects compose orthogonally

The value transform is separate from its effects. A combinator
that validates is pure computation + `Fail` effect. A combinator
that logs adds `Log`. They compose without interference:

```kea
user
  .validate()          -- -[Fail ValidationError]>
  .enrich()            -- -[IO]>
  .notify()            -- -[Send]>
-- combined effect: -[Fail ValidationError, IO, Send]>
```

The effect rows merge automatically. No manual threading. No
monad transformer stacks. No "async coloring."

---

## Structs as the Universal Unit

Kea uses structs for everything: data, modules, actors,
applications. The struct's traits determine its role.

```kea
-- A data type
struct User
  name: String
  age: Int

-- A module (stateless, singleton — zero-field struct)
struct Math
  fn abs(_ x: Int) -> Int
    if x < 0 then -x else x

-- An actor (implements Actor trait)
struct Counter
  count: Int

  fn on_message(_ self: Counter, _ msg: CounterMsg) -> Counter
    match msg
      Increment -> self~{ count: self.count + 1 }
      Decrement -> self~{ count: self.count - 1 }
      Reset     -> self~{ count: 0 }
```

The actor example shows the model perfectly: `on_message` is a
combinator. It takes the current state (a value) and a message
(a value) and returns the new state (a value). The actor runtime
handles the mailbox, the scheduling, the isolation. The
programmer writes a pure state machine.

With CoW, the actor's state update is in-place when the actor
has the only reference — which it always does (actor state is
private). So the "immutable state machine" executes with zero
allocation overhead.

---

## What You Give Up

Honest accounting. Kea's model is not free:

1. **Identity.** Mutable objects have identity — `user1 == user2`
   means "same object in memory." Kea values have equality —
   `user1 == user2` means "same field values." If you need
   identity (e.g., tracking a specific actor), you use a `Ref`
   (actor reference) or an explicit ID field.

2. **Cyclic data.** Immutable values with refcounting can't
   represent cycles (they'd leak). Kea uses `Ref` for cyclic
   relationships (actors referencing each other) and doesn't
   support cyclic immutable data.

3. **Learning curve for OOP programmers.** "Everything is
   immutable" requires rethinking patterns like "update the
   user in the database and return void." Kea's version:
   "transform the user and save the result." Same outcome,
   different shape.

4. **Some algorithms are naturally stateful.** Graph algorithms,
   in-place sorting, buffer manipulation. Kea provides `Unique T`
   for these cases — you get mutable-speed imperative code when
   you need it, contained by the type system.

These are real tradeoffs, not handwaved. But the gains —
composability, testability, parallelism safety, local reasoning,
no partial mutation, no shared mutable state — are worth it for
the vast majority of code.

---

## The Punchline

Kea's model is three ideas:

1. **Values, not objects.** Methods return new values. Composition
   is safe, testable, parallelisable.

2. **CoW makes it fast.** Immutable semantics, mutable performance.
   `Unique T` for guaranteed zero-copy when you need it.

3. **Effects, not dependencies.** IO, state, logging, failure —
   they're tracked in the type system and swapped via handlers.
   No DI containers, no mock frameworks, no global state.

Together: the programming model of a pure functional language,
the performance of an imperative one, and the tooling of neither
(because the effect system gives tools information that no other
language's type system provides).
