# Kea Idioms

How to write idiomatic Kea. These conventions emerge from the
language's design — effects, handlers, row polymorphism, and
indentation-sensitive syntax. Following them produces code that
reads naturally, composes well, and leverages the compiler.

This is a living document. Idioms are added as the language and
stdlib mature.

---

## 1. Fail is for fallibility. Result is for storage.

**Use `-[Fail E]>` in function signatures.** The return type says
what you get on success. The effect row says what can go wrong.

```kea
-- Idiomatic: return type is the success type
fn parse_config(path: String) -[IO, Fail ConfigError]> Config
  let text = IO.read_file(path)?
  let json = Json.parse(text)?
  Config.from_json(json)?

-- Unidiomatic: return type wraps success and error together
fn parse_config(path: String) -[IO]> Result(Config, ConfigError)
```

**Use Result as a data structure, not a control flow mechanism.**
Result appears when you need to store or collect outcomes:

```kea
-- Collecting results: Result is data here, not control flow
fn validate_all(items: List Item) -[Fail BatchError]> List Valid
  let results = items.map(|item| catch validate(item))
  let errors = results.filter(Result.is_err)
  if List.length(errors) > 0
    fail BatchError.validation(errors)
  results.map(Result.unwrap)
```

**`?` lifts Result back into Fail.** When you receive a Result
from `catch` or an external API, use `?` to re-enter the effect
world immediately:

```kea
let result = catch some_operation()
let value = result?   -- back in Fail-land, keep working
```

**Don't chain Result.** `Result.map`, `Result.and_then` are
monadic plumbing. In Kea, use `?` and work in the effect world:

```kea
-- Unidiomatic: monadic Result chaining
let result = Result.and_then(parse(input), |config|
  Result.map(validate(config), |valid|
    transform(valid)))

-- Idiomatic: ? and straight-line code
let config = parse(input)?
let valid = validate(config)?
transform(valid)
```

## 2. Effects are capabilities. Signatures are documentation.

**Declare effects in function signatures.** A reader should know
what a function can do from its type alone.

```kea
-- What does this function do? Read the signature:
fn process_order(order: Order) -[DB, Log, Fail OrderError]> Receipt
-- It queries a database, it logs, and it can fail. Nothing else.
```

**Separate effects by capability, not by implementation.** Don't
use a single `IO` for everything — decompose into what the function
actually needs:

```kea
-- Unidiomatic: IO covers everything
fn fetch_price(item: String) -[IO]> Int

-- Idiomatic: declares exactly what it needs
fn fetch_price(item: String) -[Net, Fail PriceError]> Int
```

**Pure functions need no annotation.** `->` means pure. If a
function has no effects, that's a guarantee the compiler enforces.

```kea
fn total(prices: List Int) -> Int
  prices.fold(0, |acc, p| acc + p)
-- Pure. Cannot do IO, cannot fail, cannot touch state.
-- The compiler proves this.
```

## 3. Handlers at the boundary. Logic in the middle.

**Business logic is effect-polymorphic.** It declares what
capabilities it needs but doesn't know how they're provided.

```kea
fn process(order: Order) -[DB, Log]> Receipt
  Log.info("Processing order {order.id}")
  let items = DB.query("SELECT * FROM items WHERE order_id = {order.id}")
  Receipt.from_items(items)
```

**Handlers live at the application edge.** `main`, request
handlers, test setup — these are where effects become concrete:

```kea
fn main() -[IO]> Unit
  let config = load_config()
  with Logging.with_stdout
  with conn <- Db.with_connection(config.db)
  let receipt = process(order)
  IO.println(receipt.show())
```

**Tests provide different handlers.** Same business logic,
different capabilities:

```kea
fn test_process()
  with mock_db(fake_items)
  with mock_logger()
  let receipt = process(test_order)
  assert(receipt.total == 42)
```

## 4. `case` over `if/else` chains.

**Use `case` for multi-branch logic.** Pattern matching is
exhaustiveness-checked and extracts values in one step.

```kea
-- Idiomatic: case with destructuring
fn describe(opt: Option Int) -> String
  case opt
    Some(n) -> "Got {n}"
    None -> "Nothing"

-- Unidiomatic: if/else chain testing the same value
fn describe(opt: Option Int) -> String
  if Option.is_some(opt)
    "Got {Option.unwrap(opt)}"
  else
    "Nothing"
```

**Use `case` on multiple values with tuples:**

```kea
fn compare(a: Int, b: Int) -> Ordering
  case (a < b, a == b)
    (true, _) -> Less
    (_, true) -> Equal
    _ -> Greater
```

## 5. Fold, map, and recursion. Not mutation.

**Use `.fold()` for accumulators:**

```kea
fn sum(xs: List Int) -> Int
  xs.fold(0, |acc, x| acc + x)

fn max(xs: List Int) -[Fail String]> Int
  case xs
    Nil -> fail "empty list"
    Cons(first, rest) -> rest.fold(first, |best, x|
      if x > best then x else best)
```

**Use `State` effect for complex stateful algorithms:**

```kea
fn tokenize(input: String) -[State Int, Fail LexError]> List Token
  -- State tracks position, Fail handles errors
  -- No mutable variables needed
```

**Use explicit recursion for recursive data:**

```kea
fn depth(tree: Tree) -> Int
  case tree
    Leaf(_) -> 1
    Branch(left, right) -> 1 + Int.max(depth(left), depth(right))
```

## 6. Subject-first style.

**Kea reads left to right.** The subject comes first, the action
comes second. This applies at every level:

```kea
-- Trait implementation: subject first
Int as Eq
  fn eq(a: Int, b: Int) -> Bool
    a == b

-- Method calls: subject.method (UMS)
xs.map(f).filter(g).fold(init, h)

-- Type annotations: value : Type
let x: Int = 42
```

## 7. `catch` for recovery. `?` for propagation.

**`?` means "I can't handle this, pass it up."** Use it when the
current function shouldn't deal with the error:

```kea
fn load(path: String) -[IO, Fail LoadError]> Data
  let text = IO.read_file(path)?   -- propagate IO failure
  let parsed = parse(text)?         -- propagate parse failure
  validate(parsed)?                 -- propagate validation failure
```

**`catch` means "I'll handle this here."** Use it when you have
a recovery strategy:

```kea
fn load_or_default(path: String) -[IO]> Config
  catch load_config(path)
    default_config()
```

**Don't catch-then-rethrow.** If you're catching just to wrap the
error, use the effect system:

```kea
-- Unidiomatic: catch, wrap, re-fail
fn load(path: String) -[IO, Fail AppError]> Config
  let result = catch load_config(path)
  case result
    Ok(config) -> config
    Err(e) -> fail AppError.config(e)

-- Idiomatic: handle the effect to transform it
fn load(path: String) -[IO, Fail AppError]> Config
  handle load_config(path)
    Fail.fail(e) -> fail AppError.config(e)
```

## 8. Doc blocks are not optional.

**Every public function gets a `doc` block.**

```kea
doc
  Find the first element satisfying the predicate.

  Returns `Some(element)` for the first match, or `None` if
  no element matches. Searches left to right.

    List.find([1, 2, 3], |x| x > 1)   -- => Some(2)
    List.find([1, 2], |x| x > 10)     -- => None
    List.find([], |_| true)            -- => None
fn find(xs: List A, pred: A -> Bool) -> Option A
```

Rules:
- First line: one sentence, starts with a verb.
- Explain edge cases and failure modes.
- At least one example showing common use.
- At least one example showing the empty/None/error case.
- Use module-qualified calls in examples (`List.find`, not `find`).

## 9. Flat `with` preambles.

**Stack handlers at the top of a block with `with`:**

```kea
fn main() -[IO]> Unit
  let config = load_config()
  with Logging.with_stdout
  with conn <- Db.with_connection(config.db)
  with Config.with_map(config.settings)
  serve(conn)
```

**`with` reads like a preamble:** "in this context, with logging,
with a database connection, with this config — do this work."

**Don't interleave `with` with other statements:**

```kea
-- Unidiomatic: with buried in the middle
do_setup()
with Logging.with_stdout     -- hard to see the handler stack
do_work()

-- Idiomatic: with at the top, work below
with Logging.with_stdout
do_setup()
do_work()
```

## 10. Name effects after capabilities, not implementations.

```kea
-- Idiomatic: what it CAN DO
effect DB
  fn query(sql: String) -> List Row

effect Log
  fn info(msg: String) -> Unit

effect Auth
  fn current_user() -> User

-- Unidiomatic: how it WORKS
effect PostgresConnection
  fn pg_query(sql: String) -> List Row

effect StdoutLogger
  fn write_log_line(msg: String) -> Unit
```

The handler decides the implementation. The effect declares the
capability. `DB` could be backed by Postgres, SQLite, or a mock.
The business logic doesn't know and doesn't care.
