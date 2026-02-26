# Kea Examples — Stress Testing the Syntax

Imaginary programs that solve real problems. The goal is to find
where the syntax sings and where it falls down.

---

## 1. Typed Actors with Backpressure

A job queue actor that accepts work, applies backpressure when
full, and returns typed results.

```kea
use Actors.{Actor, Ref, Send, Spawn}

-- The message protocol. GADT parameter T = response type.
enum QueueMsg T
  Submit(job: Job)          : QueueMsg (Result TicketId QueueFull)
  Status(id: TicketId)      : QueueMsg JobStatus
  Drain                     : QueueMsg (List JobResult)
  SetCapacity(max: Int)     : QueueMsg ()

struct QueueFull

enum JobStatus
  Pending
  Running
  Done(result: JobResult)
  Unknown

struct JobQueue
  pending: List Job
  running: Map TicketId Job
  results: Map TicketId JobResult
  capacity: Int
  next_id: Int

  fn empty(capacity: Int) -> JobQueue
    JobQueue {
      pending: [],
      running: Map.empty(),
      results: Map.empty(),
      capacity: capacity,
      next_id: 0,
    }

JobQueue as Actor
  type Msg = QueueMsg
  type Config = Int  -- initial capacity

  fn init(_ config: Int) -> JobQueue
    JobQueue.empty(config)

  fn handle(_ self: JobQueue, _ msg: QueueMsg T, _ reply: T -> Unit) -[Send]> JobQueue
    match msg
      Submit(job) ->
        if self.pending.length() + self.running.size() >= self.capacity
          reply(Err(QueueFull))
          self
        else
          let id = TicketId(self.next_id)
          reply(Ok(id))
          self~{
            pending: self.pending ++ [job~{ id: Some(id) }],
            next_id: self.next_id + 1,
          }
      Status(id) ->
        let status = if self.results.contains(id)
          then Done(result: self.results.get(id).unwrap())
          else if self.running.contains(id) then Running
          else if self.pending.any(|j| -> j.id == Some(id)) then Pending
          else Unknown
        reply(status)
        self
      Drain ->
        let all_results = self.results.values().to_list()
        reply(all_results)
        self~{ results: Map.empty() }
      SetCapacity(max) ->
        reply(())
        self~{ capacity: max }
```

### Where it works

The GADT is doing real work here. `Submit` returns
`Result TicketId QueueFull`, `Status` returns `JobStatus`, and the
compiler verifies `handle` returns the right `T` for each arm.
`Send.tell(queue, SetCapacity(100))` is legal (returns `()`).
`Send.tell(queue, Status(id))` is a type error — you'd silently
discard the `JobStatus`.

### Where it gets awkward

**The `self~{}` update inside match arms.** We can't mutate `self`,
so we're rebuilding the struct. But the match arm for `Submit`
needs to update two fields and compute a new id. This is fine for
small structs but imagine an actor with 8 fields — the update
chain gets verbose. Not a syntax problem per se, but a usability
one.

### Backpressure with deferred reply

The `reply` callback enables deferred reply — the actor stores
the callback and calls it later when capacity is available. This
maps to OTP's `noreply` + `gen_server:reply(From, Value)`:

```kea
-- A pool actor that parks callers when no connections are available
struct ConnPool
  available: List Connection
  waiting: List (Connection -> Unit)  -- parked reply callbacks

ConnPool as Actor
  type Msg = PoolMsg
  type Config = PoolConfig

  fn init(_ config: PoolConfig) -> ConnPool
    ConnPool
      available: config.connections
      waiting: []

  fn handle(_ self: ConnPool, _ msg: PoolMsg T, _ reply: T -> Unit) -[Send]> ConnPool
    match msg
      Acquire ->
        match self.available
          conn :: rest ->
            reply(conn)
            self~{ available: rest }
          [] ->
            -- Don't reply yet — park the caller
            self~{ waiting: self.waiting ++ [reply] }
      Release(conn) ->
        match self.waiting
          next :: rest ->
            next(conn)  -- unpark the oldest waiting caller
            self~{ waiting: rest }
          [] ->
            self~{ available: self.available ++ [conn] }
```

The caller writes `let conn = Send.ask(pool, Acquire)` and blocks
until the pool calls `reply(conn)` — whether that's immediate or
after another actor releases a connection.

---

## 2. DataFrame Library with @pure UDFs

A DataFusion-inspired dataframe library where user-defined
functions are `@pure` and can be lowered to DataFusion UDFs.

```kea
use Df.{DataFrame, Column, Expr, Schema}

struct Df

  --|  Read a CSV file into a DataFrame.
  fn read_csv(_ path: String) -[IO, Fail DfError]> DataFrame
    let bytes = IO.read_file(path)
    DataFrame.parse_csv(bytes)?

  --|  Run a SQL query against registered tables.
  fn sql(_ query: String) -[IO, Fail DfError]> DataFrame
    -- desugars to DataFusion logical plan
    DataFrame.from_sql(query)?

-- A scalar UDF. @pure lets the compiler verify no effects,
-- and the recipe system can lower this to a DataFusion UDF.
struct MyFunctions

  @pure
  fn normalize_email(_ email: String) -> String
    email.trim().to_lowercase()

  @pure
  fn full_name(_ first: String, _ last: String) -> String
    "{first} {last}"

  @pure
  fn clamp_score(_ score: Float, min: Float, max: Float) -> Float
    if score < min then min
    else if score > max then max
    else score

-- Usage: composing a query pipeline
struct Analytics

  fn active_user_report(_ path: String) -[IO, Fail DfError]> DataFrame
    Df.read_csv(path)
      .filter(Expr.col("active").eq(Expr.lit(true)))
      .with_column(
        "display_name",
        Expr.udf(
          MyFunctions.full_name,
          [Expr.col("first_name"), Expr.col("last_name")],
        ),
      )
      .with_column(
        "email_clean",
        Expr.udf(MyFunctions.normalize_email, [Expr.col("email")]),
      )
      .with_column(
        "score_adj",
        Expr.udf(
          MyFunctions.clamp_score,
          [Expr.col("score"), Expr.lit(0.0), Expr.lit(100.0)],
        ),
      )
      .sort_by("score_adj", descending: true)
      .limit(100)
```

### Where it works

`@pure` is doing real work. The UDFs have `->` (pure arrow), and
the recipe system can inspect them at the MIR level to verify
they're DataFusion-compatible (no closures, no heap allocation,
no recursion). The compiler already knows they're pure — the
recipe just adds the structural restrictions.

The method chaining reads nicely. `.filter().with_column().sort_by()`
is a natural left-to-right pipeline.

### Where it gets awkward

**`Expr.udf(func, [col1, col2])` is stringly-typed at the column
level.** We're passing column names as strings. If you misspell
`"first_name"` you get a runtime error, not a compile error. This
is the same problem every dataframe library has, but Kea's type
system is powerful enough that you'd expect better.

A row-polymorphic solution would look like:

```kea
-- Hypothetical: statically-typed columns via row polymorphism
fn active_user_report(_ df: DataFrame { active: Bool, first_name: String,
                                         last_name: String, email: String,
                                         score: Float | r })
  -[IO, Fail DfError]> DataFrame { display_name: String, email_clean: String,
                                     score_adj: Float | r }
```

But this breaks down immediately:
1. DataFrames can have hundreds of columns — the type signature
   is unreadable
2. DataFrame schemas are typically known at runtime (loaded from
   CSV), not compile time
3. You'd need a way to go from runtime schema → compile-time row
   type, which is fundamentally impossible without dependent types

So the string-column approach is probably correct, and the
type-safety win is at the UDF level (`@pure` functions checked
at compile time) not at the schema level.

**The `Expr.udf` call is verbose.** In Python/Pandas you'd write
`df["score"].clip(0, 100)`. Here it's
`Expr.udf(MyFunctions.clamp_score, [Expr.col("score"), Expr.lit(0.0), Expr.lit(100.0)])`.
A DSL with operator overloading might help:

```kea
-- What if Expr had arithmetic?
Expr.col("score").clamp(Expr.lit(0.0), Expr.lit(100.0))
-- or even:
col("score").clamp(0.0, 100.0)  -- with implicit Expr.lit
```

This is a library design question, not a language problem. But the
language should make it easy to build this kind of DSL. Trait-based
operator overloading (§13.2) helps.

---

## 3. HTTP Server

A simple HTTP server with middleware, routing, and JSON responses.

```kea
use Http.{Server, Request, Response, Router, Method}
use Json

struct App
  port: Int

  fn run(_ self: App) -[IO, Fail AppError]> Unit
    let router = Router.new()
      .get("/health", App.health)
      .get("/users/:id", App.get_user)
      .post("/users", App.create_user)
      .middleware(App.log_request)
      .middleware(App.cors)

    Server.listen(self.port, router)?

  fn health(_ req: Request) -[IO]> Response
    Response.json(200, #{ status: "ok" })

  fn get_user(_ req: Request) -[IO, Fail AppError]> Response
    let id = req.params.get("id").ok_or(AppError.missing_param("id"))?
    let user = Db.find_user(id)?
    Response.json(200, user)

  fn create_user(_ req: Request) -[IO, Fail AppError]> Response
    let body = Json.decode(req.body, CreateUserRequest)?
    let user = Db.insert_user(body)?
    Response.json(201, user)

  fn log_request(_ next: Handler, _ req: Request) -[IO]> Response
    let start = IO.clock_now()
    let resp = next(req)
    let elapsed = IO.clock_now() - start
    IO.stdout("{req.method} {req.path} -> {resp.status} ({elapsed}ms)")
    resp

  fn cors(_ next: Handler, _ req: Request) -[IO]> Response
    let resp = next(req)
    resp~{
      headers: resp.headers
        .insert("Access-Control-Allow-Origin", "*")
        .insert("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE"),
    }

type Handler = Request -[IO, Fail AppError]> Response

enum AppError
  NotFound(msg: String)
  BadRequest(msg: String)
  DbError(inner: Db.Error)
  JsonError(inner: Json.Error)

AppError as From Db.Error
  fn from(_ e: Db.Error) -> AppError
    AppError.DbError(inner: e)

AppError as From Json.Error
  fn from(_ e: Json.Error) -> AppError
    AppError.JsonError(inner: e)

-- The top-level entry point
struct Main
  fn main() -[IO]> Unit
    let result = catch App { port: 8080 }.run()
    match result
      Ok(()) -> ()   -- () is the unit value
      Err(e) -> IO.stdout("Server error: {e.show()}")
```

### Where it works

**Error handling is clean.** `?` propagates errors, `From` impls
convert between error types automatically. The `catch` in `main`
converts `Fail AppError` to `Result () AppError`. No exceptions,
no hidden control flow.

**Middleware is just a function.** `log_request` takes a `Handler`
and a `Request`, calls `next(req)`, and wraps the result. The
type signature tells you exactly what effects it has. No magic.

**`resp~{ headers: ... }` for functional update** on the response
is natural. You're building a new response with modified headers.

### Where it gets awkward

**The `Handler` type alias has `Fail AppError` baked in.** What
if middleware doesn't want to fail? The `cors` middleware has
`-[IO]>` but `next` returns `-[IO, Fail AppError]>`. So `cors`
needs to handle the error or propagate it. Actually looking at
this more carefully — `cors` calls `next(req)` which can fail,
but `cors` signature says `-[IO]>` (no Fail). This is a type
error! It should be:

```kea
fn cors(_ next: Handler, _ req: Request) -[IO, Fail AppError]> Response
```

This is actually effects working correctly — they caught my bug.
Every middleware that calls `next` inherits `next`'s effects. You
can't accidentally swallow an error.

**But this means every middleware must declare every effect the
handler might have.** This is where effect polymorphism helps:

```kea
fn cors(_ next: Request -[e]> Response, _ req: Request) -[e]> Response
  let resp = next(req)
  resp~{ headers: ... }
```

Now `cors` is polymorphic in `e` — it works with any handler
regardless of effects. This is much better. The effect variable
`e` captures "whatever effects the handler has, I have too."

**Router registration is stringly-typed.** `:id` in `"/users/:id"`
is a runtime convention, not a type-level guarantee. You could
misspell the param name in `req.params.get("id")` and get a
runtime error. Some frameworks solve this with type-safe routing
(like Servant in Haskell), but that's heavy machinery. The string
approach is probably right for v1.

---

## 4. Deeply Nested Effect Handlers

A request processing pipeline that layers multiple effects:
logging, database transactions, rate limiting, caching.

```kea
effect Log
  fn log(_ level: Level, _ msg: String) -> Unit

effect Tx
  fn query(_ sql: String, _ params: List Value) -> List Row
  fn execute(_ sql: String, _ params: List Value) -> Int

effect RateLimit
  fn check_rate(_ key: String, _ limit: Int) -> Unit
  -- performs Fail RateLimited if over limit

effect Cache K V
  fn cache_get(_ key: K) -> Option V
  fn cache_set(_ key: K, _ value: V) -> Unit

enum Level
  Debug
  Info
  Warn
  Error

-- A handler for Log that writes to stdout
struct Logging

  @with
  fn with_stdout(_ f: () -[Log, e]> T) -[IO, e]> T
    handle f()
      Log.log(level, msg) ->
        IO.stdout("[{level.show()}] {msg}")
        resume ()

-- A handler for Tx using a real database connection
struct Database

  @with
  fn with_transaction(_ conn: Connection, _ f: () -[Tx, e]> T)
    -[IO, Fail DbError, e]> T
    IO.stdout("BEGIN")
    let result = catch
      handle f()
        Tx.query(sql, params) ->
          let rows = conn.execute_query(sql, params)?
          resume rows
        Tx.execute(sql, params) ->
          let count = conn.execute_update(sql, params)?
          resume count
    match result
      Ok(value) ->
        IO.stdout("COMMIT")
        conn.commit()?
        value
      Err(e) ->
        IO.stdout("ROLLBACK")
        conn.rollback()?
        fail e

-- A handler for RateLimit using a cache actor
struct RateLimiter

  @with
  fn with_rate_limit(_ cache: Ref CacheMsg, _ f: () -[RateLimit, e]> T)
    -[Send, Fail RateLimited, e]> T
    handle f()
      RateLimit.check_rate(key, limit) ->
        let count = Send.ask(cache, Get(key)).unwrap_or(0)
        if count >= limit
          fail RateLimited { key: key, limit: limit }
        Send.tell(cache, Set(key, count + 1))
        resume ()

-- A handler for Cache using a Map in State
struct Caching

  @with
  fn with_map_cache(_ f: () -[Cache K V, e]> T) -[State (Map K V), e]> T
    where K: Eq
    handle f()
      Cache.cache_get(key) ->
        let m = State.get()
        resume m.get(key)
      Cache.cache_set(key, value) ->
        let m = State.get()
        State.put(m.insert(key, value))
        resume ()

-- The business logic: doesn't know about handlers
struct OrderService

  fn process_order(_ order: Order)
    -[Log, Tx, RateLimit, Cache String Price, Fail OrderError]> Receipt
    Log.log(Info, "Processing order {order.id}")

    RateLimit.check_rate(order.customer_id, limit: 10)

    -- Check cache for prices
    let prices = order.items.map(|item| ->
      match Cache.cache_get(item.sku)
        Some(price) ->
          Log.log(Debug, "Cache hit for {item.sku}")
          price
        None ->
          let rows = Tx.query(
            "SELECT price FROM products WHERE sku = ?",
            [Value.str(item.sku)],
          )
          let price = rows.first().ok_or(OrderError.unknown_sku(item.sku))?.get("price")
          Cache.cache_set(item.sku, price)
          price
    )

    let total = prices.fold(0.0, |acc, p| -> acc + p)
    let receipt_id = Tx.execute(
      "INSERT INTO receipts (order_id, total) VALUES (?, ?)",
      [Value.str(order.id), Value.float(total)],
    )

    Log.log(Info, "Order {order.id} complete: {total}")
    Receipt { id: receipt_id, order_id: order.id, total: total }

-- Wire it all up
struct Main

  fn main() -[IO]> Unit
    let conn = Db.connect("postgres://localhost/orders")?
    let cache_ref = Spawn.spawn(CacheActor, CacheActor.Config {})

    let order = Order { ... }

    -- Layer handlers from outermost to innermost:
    let result = catch
      Logging.with_stdout(|| ->
        Database.with_transaction(conn, || ->
          with_state(Map.empty(), || ->
            Caching.with_map_cache(|| ->
              RateLimiter.with_rate_limit(cache_ref, || ->
                OrderService.process_order(order)
              )
            )
          )
        )
      )

    match result
      Ok(receipt) -> IO.stdout("Success: {receipt.show()}")
      Err(e) -> IO.stdout("Failed: {e.show()}")
```

### Where it works

**The business logic is clean.** `OrderService.process_order`
just declares what effects it needs and uses them. It doesn't know
about stdout vs file logging, postgres vs sqlite, map vs redis
caching. The effects are abstract interfaces.

**Handler typing works correctly.** Each handler removes one effect
and potentially adds others:
- `with_stdout` removes `Log`, adds `IO`
- `with_transaction` removes `Tx`, adds `IO, Fail DbError`
- `with_map_cache` removes `Cache K V`, adds `State (Map K V)`
- `with_rate_limit` removes `RateLimit`, adds `Send, Fail RateLimited`

The compiler tracks all of this. By the time we're in `main`, the
only remaining effect is `IO` (plus `Fail` which we `catch`).

**Testing is straightforward.** Replace any handler:

```kea
@test
fn test_order_processing() -> Unit
  with with_test_logger
  with with_mock_db(test_fixtures())
  with with_state(Map.empty())
  with Caching.with_map_cache
  with with_mock_rate_limiter
  let result = catch OrderService.process_order(test_order())
  assert result.is_ok()
```

### Where it gets awkward (and how `with` fixes it)

**The nesting.** Five levels of handler lambdas would be painful
without sugar. But KERNEL §10.6 introduces `with` expressions
that flatten this:

```kea
with Logging.with_stdout
with Database.with_transaction(conn)
with with_state(Map.empty())
with Caching.with_map_cache
with RateLimiter.with_rate_limit(cache_ref)
let result = catch OrderService.process_order(order)

match result
  Ok(receipt) -> IO.stdout("Success: {receipt.show()}")
  Err(e) -> IO.stdout("Failed: {e.show()}")
```

Each `with` wraps everything below it as a `|| ->` callback
passed as the last argument. This desugars to the nested form
but reads flat. The `match` at the end is *outside* nothing —
it's inside all five handlers, which is correct.

**What `with` can't do:** Compose handlers into a reusable
value. Each handler has a different type (removes different
effects, adds different effects), so you can't put them in
a list or assign the composed stack to a variable. Handler
composition is syntactic (via `with`), not value-level. For
test vs production handler stacks, write separate functions
(see §3 below).

**The error type unification problem.** `with_transaction` adds
`Fail DbError`. `with_rate_limit` adds `Fail RateLimited`.
`process_order` has `Fail OrderError`. That's three different
`Fail` types. But KERNEL §5.4 says "a function may have at most
one `Fail E` in its effect set." So we need `From` impls to
unify them:

```kea
AppError as From DbError
  fn from(_ e: DbError) -> AppError
    AppError.Database(e)

AppError as From RateLimited
  fn from(_ e: RateLimited) -> AppError
    AppError.RateLimit(e)

AppError as From OrderError
  fn from(_ e: OrderError) -> AppError
    AppError.Order(e)
```

This is fine but verbose. And it means the `catch` in `main`
catches `AppError`, which is a sum of all possible errors. If you
want to handle `RateLimited` differently from `DbError`, you
pattern match on the `AppError` variants. This works but adds a
layer of wrapping/unwrapping.

**The `|| ->` lambda syntax for thunks.** Every handler takes
`() -[effects]> T`, so you write `|| ->` a lot. It's two
characters more than Haskell's `\() ->` but the `|| ->` with
the empty param list between pipes reads oddly. Maybe just
aesthetic, but it's frequent enough to notice.

---

## 5. Effect-Polymorphic Middleware Stack

What if we tried to build a composable middleware system using
effect polymorphism?

```kea
-- A middleware transforms a handler into a handler.
-- Both the input and output handlers can have different effects.
type Middleware I O = (Request -[I]> Response) -> (Request -[O]> Response)

struct Middlewares

  -- Compose two middlewares
  fn compose(
    _ outer: Middleware B C,
    _ inner: Middleware A B,
  ) -> Middleware A C
    |handler| -> outer(inner(handler))

  -- Timing middleware: adds IO for clock access
  fn timing() -> Middleware e (IO, e)
    |next| -> |req| ->
      let start = IO.clock_now()
      let resp = next(req)
      let elapsed = IO.clock_now() - start
      resp~{ headers: resp.headers.insert("X-Timing", elapsed.show()) }

  -- Auth middleware: adds Fail Unauthorized
  fn auth(_ secret: String) -> Middleware e (Fail Unauthorized, e)
    |next| -> |req| ->
      let token = req.headers.get("Authorization")
        .ok_or(Unauthorized { reason: "missing token" })?
      if not Token.verify(token, secret)
        fail Unauthorized { reason: "invalid token" }
      next(req)
```

### Where it works now (updated)

**Effect aliases and effect-parameterised types (§5.14, §11.5)
make this work.** The `Middleware I O` type alias is now valid:

```kea
type Middleware I O = (Request -[I]> Response) -> (Request -[O]> Response)
```

`I` and `O` have kind `Eff` — they're effect row parameters.
This lets you name, store, and compose middleware:

```kea
struct App E
  handler: Request -[E]> Response
  middleware: List (Request -[E]> Response -> Request -[E]> Response)
```

**What you still can't do:** Abstract over "the transformation
a handler performs" — i.e., a function from effect set to effect
set. That would require effect-set algebra (Level 4), which we've
explicitly deferred. But the `Wrap E_in E_out T` pattern from
§5.14 covers the practical cases.

---

## Summary of Findings

### Syntax wins
- **Method chaining** reads well for pipelines
- **Effect signatures** make side effects visible and the compiler
  catches real bugs (my cors middleware example)
- **GADT message protocols** give you typed actor communication
  that's genuinely better than Erlang
- **`?` and `catch`** make error handling concise
- **`@pure`** is a clean annotation for domain-specific lowering
- **Functional update `~`** is great for immutable data

### Syntax concerns
- **`with` solves handler nesting** — KERNEL §10.6 flattens the
  callback pyramid into sequential `with` statements. Requires
  `@with` annotation on target functions.
- **Single `Fail E` per effect set** means error types proliferate
  into sum types with `From` boilerplate (keep for v0, invest
  in `@derive(From)` tooling)

### Resolved since initial writing
1. ~~Effect sets aren't first-class~~ — KERNEL §5.14 adds
   effect-parameterised types (`Server E`, `Wrap E_in E_out T`).
   §11.5 adds effect row aliases (`type DbEffects = [IO, Fail DbError]`).
2. ~~Actor trait forces immediate response~~ — KERNEL §19.3 now
   uses `reply: T -> Unit` callback, enabling deferred reply (see
   ConnPool example above).
3. ~~Should there be sugar for composing handlers?~~ Yes — `with`
   (KERNEL §10.6) with `@with` opt-in annotation.
4. ~~Can effect sets be abstracted over?~~ Yes — effect row
   aliases and effect-parameterised types (§5.14, §11.5).
