# Kea for Python, TypeScript, Elixir, and Go Developers

Kea is a statically typed language with effect tracking.

That means the compiler tracks two things:
- What your values are (`String`, `User`, `List Int`, ...)
- What your functions do (`IO`, `Fail AppError`, `Send`, ...)

Most languages only enforce the first one.
Kea enforces both.

---

## Why This Exists

If you ship production systems, you already know these problems:

- A helper function quietly starts doing I/O.
- A "pure" transformation begins reading env vars.
- Error handling is inconsistent across call sites.
- Tests need mocks everywhere because side effects are hidden.
- Refactors accidentally change behavior, not just types.

Kea makes these visible in function signatures and checks them at compile time.

```kea
struct Config
  fn parse(_ text: String) -[Fail ConfigError]> Config
  fn load(_ path: String) -[IO, Fail ConfigError]> Config
```

`load` does I/O and can fail.
`parse` can fail, but does not do I/O.
That contract is enforced by the compiler.

---

## The Core Mental Model

Read function signatures as executable contracts:

- `->` means pure
- `-[IO]>` means touches the outside world
- `-[Fail E]>` means may fail with `E`
- `-[IO, Fail E]>` means both

```kea
fn format_user(_ user: User) -> String
fn fetch_user(_ id: UserId) -[IO, Fail HttpError]> User
```

If `format_user` starts calling `IO.read_file`, the compiler rejects it until the signature is updated.

---

## What This Feels Like by Background

### Python / TypeScript

You keep dynamic speed of expression, but with compile-time guarantees:
- No accidental `None`/shape bugs in core flows
- No hidden side effects inside "utility" functions
- Better refactors because contracts are explicit and checked

Think of Kea as moving common production bugs from runtime to compile time.

### Go

You already value explicitness and simple control flow.
Kea keeps explicit error modeling, but removes repetitive plumbing:
- `?` short-circuits tracked failures
- The compiler tracks effect usage automatically across call chains
- Pure functions are guaranteed pure

### Elixir

You already think in message passing and process boundaries.
Kea keeps typed actor protocols and explicit side effects:
- `Send`/`Spawn` can be tracked in signatures
- Message protocols are statically checked
- Effect handlers give you clean testing seams

---

## Before/After: What Changes in Practice

### Python/TypeScript style (hidden side effects)

Before:

```text
function parseConfig(path) {
  const text = fs.readFileSync(path, "utf8")   // hidden IO
  return JSON.parse(text)                      // may throw
}
```

After (Kea):

```kea
fn parse_config(_ path: String) -[IO, Fail ConfigError]> Config
  let text = IO.read_file(path)?
  Config.parse(text)?
```

The contract is explicit and checked.

### Go style (explicit but repetitive error plumbing)

Before:

```text
cfg, err := readConfig(path)
if err != nil { return err }
db, err := connect(cfg.URL)
if err != nil { return err }
```

After (Kea):

```kea
fn start(_ path: String) -[IO, Fail AppError]> App
  let cfg = Config.load(path)?
  let db = Database.connect(cfg.db_url)?
  App.new(cfg, db)
```

Same explicit error model, less mechanical code.

### Elixir style (dynamic message/data contracts)

Before:

```text
GenServer.call(pid, {:get_user, id})
# runtime conventions define expected reply shape
```

After (Kea):

```kea
enum UserMsg T
  Get(id: UserId) : UserMsg (Result User NotFound)

let user = Send.ask(user_ref, Get(id))
```

Reply type is encoded in the message protocol and checked statically.

---

## Opinionated Migration Strategy

Use this order. Do not start with advanced features first.

1. Mark pure core transforms with `->` and keep I/O out.
2. Move failures to `Fail E` plus `?` instead of ad-hoc exceptions.
3. Make I/O boundaries explicit with `-[IO, ...]>`.
4. Add handlers for tests where you currently monkeypatch or mock globals.
5. Introduce actor protocols only where process boundaries already exist.

If a function does three jobs (parse + fetch + mutate), split it.
Kea pays off most when signatures are narrow and honest.

---

## Do This, Not That

- Do: keep effects explicit in signatures.
- Not that: hide side effects behind "utility" functions.

- Do: use `Fail` for internal composition and convert to `Result` at boundaries.
- Not that: return `Result` everywhere by default.

- Do: use `Option` for expected absence (`None` is normal).
- Not that: use `Option` when callers need an error reason.

- Do: keep pure business logic separate from I/O orchestration.
- Not that: mix DB/network calls deep inside domain transforms.

---

## Error Handling: `Fail` and `?`

Kea keeps errors explicit without boilerplate-heavy propagation.

```kea
fn read_settings(_ path: String) -[IO, Fail SettingsError]> Settings
  let text = IO.read_file(path)?
  Settings.parse(text)?
```

`?` means:
- If `Ok`, continue.
- If `Err`, return early through `Fail`.

The compiler tracks that this function may fail with `SettingsError`.
Callers must handle or propagate it.

---

## Testing Without Global Mocking

Effects are handled explicitly, so you can swap implementations by scope.

```kea
fn with_mock_fs(_ files: Map String String, _ f: () -[IO, e]> T) -[e]> T
  handle f()
    IO.read_file(path) ->
      resume files.get(path).unwrap_or("")
```

Production code uses real `IO`.
Tests can run the same code with a local handler.
No global monkeypatching, no fragile DI container setup.

---

## Type System Value (Without Theory First)

Kea's type system gives practical guarantees:

- Exhaustive pattern matching: no forgotten cases
- Flexible records: require only fields you actually use
- Trait-based capabilities: generic code without losing safety
- Effect transparency: higher-order functions preserve caller effects

Example of flexible records:

```kea
fn greet(_ x: { name: String | r }) -> String
  "Hello, {x.name}"
```

Works with any value that has a `name` field.
No inheritance hierarchy required.

---

## What Kea Is Not Trying to Be

- It is not "dynamic language ergonomics with optional checks."
- It is not "exceptions everywhere and hope tests catch it."
- It is not "a giant effect framework hidden in libraries."

The language itself tracks behavior contracts.

---

## A Practical Migration Path

1. Start with pure data transforms and explicit types at boundaries.
2. Add `Fail` tracking for error-heavy workflows.
3. Move I/O-heavy paths to explicit `-[IO, ...]>` signatures.
4. Introduce handlers for test isolation.
5. Gradually use trait capabilities and actor protocols where needed.

You do not need to learn every advanced feature on day one.

---

## One-Line Summary

Kea lets the compiler verify what your code does, not just what your values are.
