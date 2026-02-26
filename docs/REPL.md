# Kea REPL Design

The Kea REPL is an interactive environment where the type system, effect system, and actor library are not just checked but *explored*. Every feature is a projection of information the compiler and runtime already have.

---

## 1. Design Thesis

Kea's architecture gives the REPL access to information no other general-purpose REPL has: inferred types with full effect sets at every expression, handler composition visible before execution, actor state and supervision trees observable live, and row-polymorphic records that unify structurally.

**The core interaction model is type-and-effect-aware exploration.** In every other compiled language's REPL, the cycle is: write, compile, run, see result. In Kea, the compiler is always running — effects are inferred as you type, handler composition is checked before you press enter, and the runtime integrates seamlessly with the interactive loop via handlers.

**Effects make the REPL honest.** Every expression shows not just its type but its effects. You see exactly what a function *does* — not just what it returns. When you handle an effect, you see the effect set shrink. When you compose handlers, you see the full pipeline of what's being intercepted. No other REPL shows you this.

**Handlers make the REPL a laboratory.** The same effectful computation can be run under different handlers without changing the computation itself. Test an IO function with mock handlers. Run a stateful computation with different initial states. Try different logging strategies. The REPL is where you experiment with handlers before committing to them.

**Actors make the REPL a control room.** Actors spawned at the REPL persist across lines. You can send them messages, inspect their state, observe supervision trees, and build distributed systems interactively. The actor dashboard is a live view over a running system.

---

## 2. REPL Architecture

### 2.1 Compilation Model

Kea is a compiled language. The REPL compiles each input to native code via Cranelift, executes it, and displays the result. This is not a tree-walking interpreter — it's JIT compilation of each REPL expression.

The type environment and the runtime environment both persist across REPL lines. Bindings, type definitions, effect declarations, trait implementations, and actor handles all accumulate.

```
Input → Lex → Parse → Type-check → Lower to MIR → Cranelift JIT → Execute → Display
                ↑                         ↑
        persistent TypeEnv        persistent RuntimeEnv
```

### 2.2 Indentation Handling

Kea uses indentation-sensitive syntax. The REPL handles multi-line input:

**Automatic continuation.** Lines ending with keywords that introduce blocks (`fn`, `struct`, `match`, `if`, `handle`, `effect`, `enum`, `trait`, `for`) or ending with an operator (`=`, `->`, `-[`, `,`) trigger multi-line mode. The prompt changes to `....` with auto-indentation at the expected level.

**Block termination.** A blank line at indent level 0 (or a dedent past the outermost block) terminates the multi-line input and submits it.

**Paste detection.** Rapid input (multiple lines arriving within a short time window) triggers paste mode. The REPL buffers the entire paste, then processes it as a single input. This prevents line-by-line evaluation of pasted blocks.

**History as blocks.** Up-arrow on a multi-line definition recalls the entire block as a unit, not line-by-line. The block can be edited as a whole and resubmitted.

**`:edit` escape hatch.** For substantial definitions, `:edit` opens `$EDITOR` with the current input or a named binding's definition. If the editor supports LSP and Kea's LSP server is running, the temp `.kea` file gets full autocompletion and diagnostics.

**Spaces only.** Tabs in indentation are a parse error. Eliminates mixing issues. Two spaces per indent level (matching the KERNEL examples).

### 2.3 Input Classification

The REPL classifies each input before processing:

| Input starts with | Classification | Action |
|---|---|---|
| `let` | Binding | Type-check, compile, execute, bind name, show `name : Type  effects: [...]` |
| `fn` | Function definition | Type-check, compile, bind, show `name : Signature` |
| `struct` | Struct definition | Register type, show name and fields |
| `enum` | Enum definition | Register type, show name and variants |
| `effect` | Effect declaration | Register effect, show operations |
| `trait` | Trait definition | Register trait, show methods |
| `impl` | Trait implementation | Type-check, register, show confirmation |
| `handle` | Handler expression | Type-check (effect removal), compile, execute |
| `use` | Import | Resolve, bring names into scope |
| `:` prefix | REPL command | Dispatch to command handler |
| anything else | Expression | Type-check, compile, execute, show `value : Type  effects: [...]` |

---

## 3. Default Display

### 3.1 Expressions

Every evaluated expression shows its value, type, and effect set:

```
kea> 1 + 2
3 : Int

kea> "hello".String::len()
5 : Int

kea> #{ name: "alice", age: 30 }
#{ name: "alice", age: 30 } : #{ name: String, age: Int }
```

Pure expressions show type only. Effectful expressions show effects:

```
kea> IO.read_file("config.toml")
<Bytes 2.4KB> : Bytes  effects: [IO, Fail IOError]
```

### 3.2 Bindings

```
kea> let x = 42
x : Int

kea> let config = IO.read_file("config.toml")
config : Bytes  effects: [IO, Fail IOError]
```

### 3.3 Function Definitions

```
kea> fn greet(_ name: String) -> String
....   "Hello, {name}!"
greet : String -> String

kea> fn load(_ path: String) -[IO, Fail FileError]> Config
....   let data = IO.read_file(path)
....   Config.parse(data)?
load : String -[IO, Fail FileError]> Config
```

When effects are inferred (no annotation), the REPL shows what was inferred:

```
kea> fn load_config(_ path: String)
....   let data = IO.read_file(path)
....   Config.parse(data)?
load_config : String -[IO, Fail FileError]> Config
  -- inferred: IO from IO.read_file, Fail FileError from ?
```

The `-- inferred:` line explains *where each effect came from*. This is teaching material — the user learns to read effect sets by seeing how they're composed.

### 3.4 Effect Declarations

```
kea> effect Log
....   fn log(_ level: Level, _ msg: String) -> Unit
effect Log
  log : (Level, String) -> Unit
```

### 3.5 Type Definitions

```
kea> struct Point
....   x: Float
....   y: Float
....
....   fn distance(_ self, _ other: Point) -> Float
....     ((self.x - other.x) ** 2.0 + (self.y - other.y) ** 2.0).Float::sqrt()
Point { x: Float, y: Float }
  distance : (Point, Point) -> Float

kea> enum Shape
....   Circle(Float)
....   Rect(Float, Float)
Shape = Circle(Float) | Rect(Float, Float)
```

---

## 4. Effect Exploration

This is the REPL's distinctive feature. No other language REPL shows you effect composition interactively.

### 4.1 Effect Tracking Display

Every expression shows its effect set. As you build up computations, you see effects accumulate:

```
kea> IO.read_file("data.csv")
-- : Bytes  effects: [IO, Fail IOError]

kea> let data = IO.read_file("data.csv")
data : Bytes  effects: [IO, Fail IOError]

kea> let result = catch IO.read_file("data.csv")
result : Result Bytes IOError  effects: [IO]
-- catch removed Fail IOError, IO remains
```

The REPL annotates handler applications with what changed — which effects were removed, which were added. This is the moment the effect system clicks for a new user.

### 4.2 Handler Exploration

The same computation can be run under different handlers. The REPL shows the effect transformation at each step:

```
kea> let program = || -> Log.log(Info, "hello") ; IO.stdout("world")
program : () -[Log, IO]> Unit

kea> -- Try handler 1: silent logging
kea> handle program()
....   Log.log(_, _) -> resume ()
"world"
: ()  effects: [IO]
-- Log handled (silently), IO passed through

kea> -- Try handler 2: stdout logging
kea> fn with_stdout_log(_ f: () -[Log, e]> T) -[IO, e]> T
....   handle f()
....     Log.log(level, msg) ->
....       IO.stdout("[{level}] {msg}")
....       resume ()
with_stdout_log : (() -[Log, e]> T) -[IO, e]> T

kea> with_stdout_log(program)
[Info] hello
world
: ()  effects: [IO]
-- Log handled via with_stdout_log, added IO, IO from program merged
```

### 4.3 `:effects` Command

Show the effect set of any expression or binding without executing:

```
kea> :effects load_config("foo.toml")
String -[IO, Fail FileError]> Config
  IO         from IO.read_file (line 2 of load_config)
  Fail FileError  from ? operator (line 3 of load_config)

kea> :effects catch load_config("foo.toml")
effects: [IO]
  IO         from IO.read_file (line 2 of load_config)
  Fail FileError  removed by catch
```

This is purely a type-system query — no execution, no cost. The compiler has the information; the REPL renders it.

### 4.4 `:handlers` Command

List available handlers for a given effect:

```
kea> :handlers Fail
Handlers for Fail E:
  catch expr           -- converts Fail E to Result T E
  match/catch pattern  -- catch with pattern matching on error type

kea> :handlers Log
Handlers for Log:
  with_stdout_log      -- Log.log → IO.stdout        effects: adds [IO]
  with_file_log        -- Log.log → IO.write_file    effects: adds [IO]
  with_silent_log      -- Log.log → ()               effects: adds []
  (define your own with `handle`)
```

This queries the type environment for functions whose signatures consume a given effect — functions of the form `(() -[E, e]> T) -[e, H...]> T`.

### 4.5 Mock Handler Workflow

The REPL is the natural place to test effectful code with mock handlers:

```
kea> -- Define a function that does real IO
kea> fn process_file(_ path: String) -[IO, Fail AppError]> Report
....   let raw = IO.read_file(path)
....   let parsed = Parser.parse(raw)?
....   Report.generate(parsed)

kea> -- Test it with mocks at the REPL
kea> let mock_data = "col1,col2\n1,2\n3,4".Bytes::from_string()

kea> let result = catch
....   handle process_file("test.csv")
....     IO.read_file(_) -> resume mock_data
....     IO.write_file(_, _) -> resume ()
....     IO.stdout(_) -> resume ()
....     IO.clock_now() -> resume (Timestamp.epoch())
result : Result Report AppError  effects: []
-- All effects handled. Pure result. No actual IO occurred.
```

The handler removed `IO`, `catch` removed `Fail`. The result is pure — testable, deterministic, no side effects. This is the primary testing workflow for effectful code, and the REPL is where you develop the mock handlers.

### 4.6 Effect Provenance in Errors

When a type error involves effects, the REPL shows provenance:

```
kea> fn pure_function(_ x: Int) -> Int
....   IO.stdout("debug: {x}")
....   x * 2

error: function declared pure (->) but body has effects [IO]
  --> <repl>:2
  │
2 │   IO.stdout("debug: {x}")
  │   ^^^^^^^^^^^^^^^^^^^^^^^^ IO effect introduced here
  │
  help: add effect annotation: fn pure_function(_ x: Int) -[IO]> Int
        or use Log effect for debug output: Log.log(Debug, "debug: {x}")
```

---

## 5. Actor Interaction

Actors are library-level (kea-actors), built on `Send` and `Spawn` effects. The REPL integrates them as first-class interactive objects.

### 5.1 Spawning and Messaging

```
kea> struct Counter
....   count: Int
....
....   fn init(_ config: ()) -> Counter
....     Counter { count: 0 }
....
....   fn handle(_ self: Counter, _ msg: CounterMsg T) -[Send]> (Counter, T)
....     match msg
....       Increment -> (Counter { count: self.count + 1 }, ())
....       Decrement -> (Counter { count: self.count - 1 }, ())
....       Get -> (self, self.count)

kea> enum CounterMsg T
....   Increment : CounterMsg ()
....   Decrement : CounterMsg ()
....   Get       : CounterMsg Int

kea> let counter = Spawn.spawn(Counter, ())
counter : Ref CounterMsg  effects: [Spawn]

kea> Send.tell(counter, Increment)
: ()  effects: [Send]

kea> Send.tell(counter, Increment)
: ()  effects: [Send]

kea> Send.ask(counter, Get)
2 : Int  effects: [Send]
```

Actors persist across REPL lines. The REPL runtime handles `Send` and `Spawn` effects — it *is* the actor runtime for interactive use.

### 5.2 `:actors` Dashboard

```
kea> :actors
  #  Name            Type      Status   Mailbox   Uptime
  1  counter         Counter   running  0/256     2m 14s
  3  logger          Logger    running  0/256     1m 30s
  4  supervisor_1    Supervisor running  0/256     1m 30s
    └─ 3  logger    (child)

2 actors running, 1 supervisor
```

### 5.3 `:inspect` Actor State

```
kea> :inspect counter
Actor #1: Counter
  Status:  running
  State:   Counter { count: 2 }
  Mailbox: 0/256 (empty)
  Uptime:  2m 14s
  Messages processed: 3 (2 tell, 1 ask)
  Supervisor: none (top-level)
```

`:inspect` renders the actor's current state using its `Show` implementation. This requires the actor type to derive or implement `Show` — the REPL warns if it can't inspect:

```
kea> :inspect opaque_actor
Actor #5: SecureStore
  Status: running
  State:  (SecureStore does not implement Show — cannot inspect)
```

### 5.4 `:send` Shorthand

For interactive exploration, `:send` is sugar for `Send.tell` / `Send.ask`:

```
kea> :send counter Increment
: ()

kea> :send counter Get
2 : Int
```

### 5.5 Actor Lifecycle in the REPL

Actors spawned at the REPL follow the same lifecycle as in production code. On REPL exit, the runtime performs ordered shutdown (supervisors drain children first). Ctrl-C sends a shutdown signal; a second Ctrl-C forces immediate termination.

```
kea> :quit
Shutting down 3 actors...
  #4 supervisor_1: draining children
    #3 logger: stopped (graceful)
  #4 supervisor_1: stopped (graceful)
  #1 counter: stopped (graceful)
Bye!
```

---

## 6. Handler Composition Patterns

The REPL is the laboratory for understanding how handlers compose. This is where Kea's effect system goes from theoretical to intuitive.

### 6.1 Layered Handlers

```
kea> fn app() -[Log, State Int, IO]> Unit
....   Log.log(Info, "starting")
....   State.put(State.get() + 1)
....   IO.stdout("count: {State.get()}")

kea> -- Handle one effect at a time, watch the set shrink
kea> :effects app()
effects: [Log, State Int, IO]

kea> :effects with_stdout_log(app)
effects: [State Int, IO]
-- Log handled, added IO (merged with existing IO)

kea> :effects with_state(0, || -> with_stdout_log(app))
effects: [IO]
-- State Int handled, Log handled via stdout

kea> -- Now execute the fully handled computation
kea> with_state(0, || -> with_stdout_log(app))
[Info] starting
count: 1
: ((), 1)  effects: [IO]
```

Each handler peels off one layer. The REPL shows the effect set shrinking at each step. By the time you run it, you understand exactly what each handler is doing.

### 6.2 Handler Comparison

Different handlers for the same effect produce different behaviour. The REPL makes this concrete:

```
kea> fn computation() -[State Int]> Int
....   State.put(10)
....   let x = State.get()
....   State.put(x + 5)
....   State.get()

kea> -- Handler A: mutable state via Unique
kea> with_state(0, computation)
(15, 15) : (Int, Int)

kea> -- Handler B: state as pure function (logged)
kea> fn with_logged_state(_ initial: S, _ f: () -[State S, e]> T) -[IO, e]> (T, S)
....   let state = Unique initial
....   let result = handle f()
....     State.get() ->
....       IO.stdout("  State.get() -> {state.freeze()}")
....       resume state.freeze()
....     State.put(new_state) ->
....       IO.stdout("  State.put({new_state})")
....       state = new_state
....       resume ()
....   (result, state.freeze())

kea> with_logged_state(0, computation)
  State.put(10)
  State.get() -> 10
  State.put(15)
  State.get() -> 15
(15, 15) : (Int, Int)  effects: [IO]
```

Same computation, different handlers, different observable behaviour. This is how you teach the effect system — not by reading papers, but by watching handlers transform execution.

### 6.3 `:trace_effects` Command

For complex handler stacks, trace every effect operation as it's dispatched:

```
kea> :trace_effects with_state(0, || -> with_stdout_log(app))
  [1] Log.log(Info, "starting")
      → handled by with_stdout_log → IO.stdout("[Info] starting")
      → IO handled by runtime
  [2] State.get()
      → handled by with_state → resume 0
  [3] State.put(1)
      → handled by with_state → resume ()
  [4] State.get()
      → handled by with_state → resume 1
  [5] IO.stdout("count: 1")
      → IO handled by runtime
: ((), 1)  effects: [IO]
```

This is the effect equivalent of a debugger's step-through. Every effect operation is shown, along with which handler caught it and what it did. Invaluable for understanding complex handler stacks.

---

## 7. Type Exploration

### 7.1 `:type` Command

Show the type of any expression without executing:

```
kea> :type List.map
(List T, (T -> U)) -> List U

kea> :type List.filter
(List T, (T -> Bool)) -> List T

kea> :type Send.ask
(Ref M, M T) -[Send]> T
```

### 7.2 `:info` Command

Show everything known about a name — type, effects, traits, source:

```
kea> :info List.map
fn map(_ list: List T, _ f: T -> U) -> List U

  Type:     (List T, (T -> U)) -> List U
  Effects:  pure (->)
  Defined:  kea-core/src/list.kea:47
  Traits:   requires nothing
  Doc:      Apply f to each element, returning a new list.

kea> :info Counter
struct Counter
  count: Int

  Inherent methods:
    init     : () -> Counter
    handle   : (Counter, CounterMsg T) -[Send]> (Counter, T)

  Implements:
    Actor (Msg = CounterMsg, Config = ())
    Show
```

### 7.3 `:instances` Command

Show all implementations of a trait:

```
kea> :instances Show
Show is implemented by:
  Int             (built-in)
  Float           (built-in)
  String          (built-in)
  Bool            (built-in)
  Option T        (where T: Show)
  Result T E      (where T: Show, E: Show)
  List T          (where T: Show)
  #{ ... }        (where all fields: Show)
  Point           (derived)
  Counter         (derived)
  Shape           (derived)
```

### 7.4 `:unify` Command

Check if two types unify and show the substitution:

```
kea> :unify #{ x: Int, y: Float | r } and #{ x: Int, y: Float, z: String }
Unifies: yes
  r := #{ z: String }

kea> :unify List Int and List String
Unifies: no
  Int ≠ String at position 1
```

This is directly useful for understanding row polymorphism — you can test whether a function accepts a given record type.

### 7.5 `:accepts` Command

Check if a function accepts given arguments:

```
kea> :accepts List.filter with [1, 2, 3] and (|x| -> x > 1)
Yes: List.filter([1, 2, 3], |x| -> x > 1) : List Int  effects: []

kea> :accepts List.filter with "hello" and (|x| -> x > 1)
No: expected List T, got String
```

---

## 8. Session Management

### 8.1 `:env` Command

List all bindings with types and effects:

```
kea> :env
  x         : Int
  config    : Bytes                      effects: [IO, Fail IOError]
  counter   : Ref CounterMsg             effects: [Spawn]
  greet     : String -> String
  load      : String -[IO, Fail FileError]> Config
  Point     : struct { x: Float, y: Float }
  Shape     : enum (Circle | Rect)
  Log       : effect (log)
  Counter   : struct { count: Int }  implements Actor

9 bindings (4 values, 3 functions, 2 types)
```

### 8.2 Undo/Redo

Binding-level undo. Each `let`, `fn`, `struct`, `enum`, `effect`, `trait`, `impl` is a semantic checkpoint:

```
kea> let a = 1
kea> let b = 2
kea> let c = a + b

kea> :undo
-- Removed: c
-- Session: a, b

kea> :undo
-- Removed: b
-- Session: a

kea> :redo
-- Restored: b
-- Session: a, b
```

Undoing a binding propagates: if `c` depends on `b`, undoing `b` also marks `c` as stale.

### 8.3 `:reset`

Clear the session entirely:

```
kea> :reset
Session cleared. Prelude re-loaded.
```

### 8.4 `:export`

Export the current session as a valid `.kea` file:

```
kea> :export my_module.kea
-- Exported 6 definitions (topologically sorted)
-- Excluded: 2 exploratory bindings not in dependency chain
-- Written: my_module.kea (45 lines)
```

The export is the minimal set of definitions needed to reproduce the session's outputs, topologically sorted, with dead ends pruned. A valid Kea source file.

---

## 9. Testing at the REPL

### 9.1 Effectful Testing with Handlers

The canonical testing pattern: handle all effects, assert on pure results.

```
kea> fn test_load_config()
....   let mock_fs = Map.from_list([
....     ("config.toml", "port = 8080".Bytes::from_string())
....   ])
....   let result = catch
....     handle load_config("config.toml")
....       IO.read_file(path) ->
....         match mock_fs.get(path)
....           Some(data) -> resume data
....           None -> Fail.fail(FileError.not_found(path))
....   match result
....     Ok(config) -> assert_eq(config.port, 8080)
....     Err(e) -> assert false "unexpected error: {e}"

test_load_config : () -> Unit
-- pure! All effects handled by mocks.

kea> test_load_config()
: ()
-- passed
```

### 9.2 Property Testing with Effects

```
kea> fn prop_state_get_returns_last_put(_ seed: Int)
....   let value = Rand.random_int(seed, 0, 1000)
....   with_state(0, || ->
....     State.put(value)
....     assert_eq(State.get(), value)
....   )

kea> :property prop_state_get_returns_last_put iterations: 100
100/100 passed
```

### 9.3 `:bench` Microbenchmarking

```
kea> :bench List.sort(big_list)
  median: 1.24ms  p99: 1.89ms  iterations: 1000

kea> :bench big_list.sort()  -- same thing via method syntax
  median: 1.24ms  p99: 1.89ms  iterations: 1000
```

Useful for testing handler compilation performance — compare the same computation under different handler strategies:

```
kea> :bench with_state(0, || -> state_heavy_computation())
  median: 45μs  p99: 67μs  iterations: 10000

kea> :bench with_logged_state(0, || -> state_heavy_computation())
  median: 1.2ms  p99: 1.8ms  iterations: 1000
-- ~26x slower due to IO in handler
```

---

## 10. MCP Integration

The REPL's MCP server exposes the full type and effect environment to LLM agents. This is the same MCP server used during compiler development, adapted for interactive use.

### 10.1 MCP Tools

| Tool | Description | Returns |
|---|---|---|
| `type_check` | Type-check a Kea expression | Type, effect set, diagnostics |
| `get_type` | Look up a name's type | Type scheme |
| `get_effects` | Analyse effect set of an expression | Effect set with provenance |
| `evaluate` | Compile and execute an expression | Value, type, effects |
| `diagnose` | Get detailed error analysis | Diagnostics with suggestions |
| `list_handlers` | Find handlers for an effect | Handler signatures |
| `list_bindings` | Current session bindings | Names, types, effects |
| `actor_status` | Query actor state | Status, mailbox, uptime |

### 10.2 MCP Resources

| Resource | Description |
|---|---|
| `session://bindings` | Live binding list (name, type, effects) |
| `session://actors` | Live actor table (id, type, status, mailbox) |
| `session://effects` | All effects in scope with their operations |
| `session://types` | All types in scope with their methods |

### 10.3 LLM Collaboration via `:ask`

```
kea> :ask "handle all effects in process_file so I can test it"

-- Proposed:
fn test_process_file(_ mock_data: Bytes) -> Result Report AppError
  catch
    handle process_file("test.csv")
      IO.read_file(_) -> resume mock_data
      IO.write_file(_, _) -> resume ()
      IO.stdout(_) -> resume ()
      IO.clock_now() -> resume (Timestamp.epoch())

-- Type check: ok
-- Effects: [] (all handled)
-- [run]  [edit]  [explain]
```

The LLM has access to the session's type environment and effect declarations. It knows which effects `process_file` has, which handler operations are needed, and can generate a complete mock handler that the type checker verifies before execution.

### 10.4 Indentation in MCP

MCP tools receive code as JSON string payloads. Whitespace (including indentation) is preserved in JSON string values. The MCP `type_check` tool gives immediate feedback on indentation errors — same diagnostics as any other parse error. The agent-fix loop (submit → error → fix → resubmit) works identically to how it works for any other syntax issue.

---

## 11. Rich Display

### 11.1 Syntax Highlighting

The REPL highlights input using the lexer (same approach as Rill). Keywords in bold blue, strings in green, numbers in yellow, type names in cyan, effect annotations in magenta.

### 11.2 Type-Coloured Output

Values in output are coloured by type. `Int` in yellow, `String` in green, `Bool` in cyan, constructors in bold. Effect sets in magenta brackets. This makes complex nested values scannable.

### 11.3 Collection Display

```
kea> List.range(1, 100)
[1, 2, 3, 4, 5, ... 96, 97, 98, 99, 100] : List Int
-- 100 elements

kea> Map.from_list([("a", 1), ("b", 2), ("c", 3)])
{ "a": 1, "b": 2, "c": 3 } : Map String Int
-- 3 entries
```

Large collections show head + tail with count. `:explore` for the full view.

### 11.4 Record Display

```
kea> #{ name: "alice", age: 30, active: true, scores: [95, 87, 92] }
#{ name: "alice"
   age: 30
   active: true
   scores: [95, 87, 92] }
: #{ name: String, age: Int, active: Bool, scores: List Int }
```

Records with more than 3 fields display vertically. Nested records indent further.

### 11.5 Enum Display

```
kea> Some(42)
Some(42) : Option Int

kea> Err("not found")
Err("not found") : Result _ String
```

### 11.6 Effect Set Display

Effect sets are always shown in a consistent order (alphabetical by effect name), with parameterised effects showing their type arguments:

```
effects: [Alloc, Fail ParseError, IO, Log, Send, State Config]
```

In interactive output, the REPL uses colour and can optionally show provenance:

```
effects: [IO, Fail FileError]
         ──  ──────────────
         │        └─ from Config.parse (line 3) via ? operator
         └─ from IO.read_file (line 2)
```

---

## 12. Commands Reference

### Core Commands

| Command | Description |
|---|---|
| `:help` | Show available commands |
| `:quit` or Ctrl-D | Exit the REPL |
| `:type <expr>` | Show type without executing |
| `:effects <expr>` | Show effect set with provenance |
| `:info <name>` | Full information about a name |
| `:env` | List all session bindings |
| `:edit [name]` | Open `$EDITOR` for multi-line editing |

### Type System Commands

| Command | Description |
|---|---|
| `:instances <Trait>` | List all implementations of a trait |
| `:unify <type1> and <type2>` | Check type unification |
| `:accepts <fn> with <args>` | Check if function accepts arguments |
| `:trace <Type> <Trait>` | Explain why a type does/doesn't implement a trait |

### Effect Commands

| Command | Description |
|---|---|
| `:handlers <Effect>` | List available handlers for an effect |
| `:trace_effects <expr>` | Execute with effect operation tracing |
| `:mock <Effect>` | Generate a mock handler skeleton |

### Actor Commands

| Command | Description |
|---|---|
| `:actors` | Show actor dashboard |
| `:inspect <actor>` | Show actor's current state |
| `:send <actor> <msg>` | Send a message to an actor |
| `:stop <actor>` | Gracefully stop an actor |
| `:supervision` | Show supervision tree |

### Session Commands

| Command | Description |
|---|---|
| `:undo` | Undo last binding |
| `:redo` | Redo undone binding |
| `:reset` | Clear session |
| `:export <file>` | Export session to `.kea` file |
| `:load <file>` | Load a `.kea` file into session |

### Testing Commands

| Command | Description |
|---|---|
| `:bench <expr>` | Microbenchmark an expression |
| `:property <fn> iterations: N` | Run property test |
| `:test <fn>` | Run a test function and report pass/fail |

### LLM Commands

| Command | Description |
|---|---|
| `:ask "<natural language>"` | Generate code from description |

---

## 13. Indentation-Specific REPL Behaviour

### 13.1 Multi-Line Continuation Rules

The REPL enters multi-line mode when:

1. **Block-introducing keyword at end of logical line:** `fn`, `struct`, `enum`, `effect`, `trait`, `impl`, `match`, `handle`, `if`, `for`. The next line auto-indents by 2 spaces.

2. **Trailing operator:** `=`, `->`, `-[`, `,`, `++`, and binary operators at end of line. The next line continues at the same or greater indent.

3. **Unclosed delimiters:** `(`, `[`, `{` without matching close. The next line auto-indents.

4. **Explicit continuation:** Backslash at end of line (escape hatch, discouraged).

### 13.2 Block Termination

Multi-line mode exits when:

1. **Blank line at indent level 0.** This is the primary termination signal.

2. **Dedent past the outermost block.** If you dedent to column 0 with a non-blank line, the previous block is closed and the new line starts a new top-level input.

3. **Two consecutive blank lines.** Safety valve — always terminates regardless of indent level.

### 13.3 Continuation Prompt

```
kea> fn greet(_ name: String) -> String
....   "Hello, {name}!"
....
greet : String -> String

kea> handle program()
....   Log.log(level, msg) ->
....     IO.stdout("[{level}] {msg}")
....     resume ()
....
: ()  effects: [IO]
```

The `....` prompt indicates continuation. Its length matches `kea> ` for alignment. The cursor is auto-positioned at the expected indent level.

### 13.4 Paste Mode

Paste detection (multiple lines arriving within ~50ms) activates paste mode:

```
kea> [paste mode]
  struct Server
    host: String
    port: Int

    fn address(_ self) -> String
      "{self.host}:{self.port}"
[end paste — 6 lines]
Server { host: String, port: Int }
  address : Server -> String
```

In paste mode, blank lines within the paste don't terminate input — only the end of the paste buffer does.

---

## 14. Startup and Configuration

### 14.1 Startup Sequence

```
$ kea
Kea v0.1.0
Type :help for commands, Ctrl-D to exit.

kea>
```

If run inside a project directory (with `kea.toml`), the REPL loads the project's dependencies and brings them into scope:

```
$ cd my-project && kea
Kea v0.1.0 (my-project)
Loaded: kea-actors 0.1.0, kea-json 0.1.0
Type :help for commands, Ctrl-D to exit.

kea>
```

### 14.2 Configuration

`~/.config/kea/repl.toml`:

```toml
[repl]
edit_mode = "vi"          # or "emacs" (default)
history_file = "~/.local/share/kea/history"
max_history = 10000
show_effect_provenance = true   # show where effects come from
show_inferred_effects = true    # show "-- inferred:" on fn definitions
color = "auto"                  # "auto", "always", "never"

[repl.display]
max_collection_items = 20       # truncate collections
max_record_fields_inline = 3    # vertical display threshold
max_string_length = 200         # truncate long strings
```

### 14.3 Prelude

The REPL prelude brings into scope everything from `kea-core`'s prelude (Appendix C of KERNEL): core traits (`Show`, `Eq`, `Ord`, `Hash`, `From`, `Into`, `Default`), core types (`Option`, `Result`, `List`, `Map`, `Set`, `String`, `Bytes`), core effects (`IO`, `Fail`), and assertion functions (`assert`, `assert_eq`, `assert_ne`).

Additional libraries are available via `use`:

```
kea> use kea_actors (Actor, Ref, Send, Spawn)
imported Actor, Ref, Send, Spawn from kea_actors

kea> use kea_log (Log, Level)
imported Log, Level from kea_log
```

---

## 15. Sequencing

Ordered by dependency and impact:

1. **Input loop with multi-line indentation handling.** The foundation. Correct INDENT/DEDENT in the REPL determines whether the language feels usable interactively. Paste mode essential.

2. **Type + effect display on every expression.** The "aha" moment. Every expression shows its type and effect set. Pure expressions show nothing extra; effectful expressions show their effects. This is where Kea's effect system becomes tangible.

3. **`:type` and `:effects` commands.** Zero-cost type and effect queries. No execution. The compiler already has the information — just render it.

4. **`:info` and `:env`.** Session awareness. Know what's in scope, what types and effects are available, what bindings exist.

5. **Handler expressions at the REPL.** `handle` expressions compile and execute interactively. The effect set transformation is shown. This is where handler composition becomes intuitive.

6. **Actor spawning and messaging.** `Spawn.spawn` and `Send.tell`/`Send.ask` work at the REPL. Actors persist across lines. The runtime provides the handler for `Send` and `Spawn`.

7. **`:actors` and `:inspect`.** Actor dashboard and state inspection. Live view of the actor system.

8. **`:handlers` and `:trace_effects`.** Effect exploration tools. Find handlers for an effect; trace effect dispatch through a handler stack.

9. **`:export` and `:load`.** Session persistence. Export exploration as valid Kea source; load source files into the session.

10. **`:undo`/`:redo`.** Session editing. Binding-level undo with dependency propagation.

11. **`:bench` and `:property`.** Testing tools. Microbenchmarking for handler performance comparison; property testing with effect-aware generators.

12. **MCP server integration.** `:ask` and programmatic access to the type/effect environment. The MCP server runs alongside the REPL from day one (Phase 0b of the roadmap), but the interactive `:ask` command is a polish item.

13. **`:mock` generator.** Given a function's effect set, generate a skeleton mock handler with all operations stubbed out. Reduces boilerplate for testing.

14. **`:trace` for trait provenance.** Explain why a type does or doesn't implement a trait — same as Rill's `rill doc --trace`, adapted for effects.

15. **Rich TUI overlays.** `:explore` for collections, `:supervision` as interactive tree, `:actors` as live dashboard. Ratatui-based. Important for actors; optional for everything else.

---

## 16. Design Principles

- **Effects are first-class in the display.** Every expression shows its effect set. This is non-negotiable — it's the defining feature of Kea's REPL. If effects are hidden, the effect system is invisible, and the language's core innovation becomes theoretical rather than practical.

- **Handlers are the REPL's superpower.** The ability to run the same computation under different handlers is the interactive equivalent of dependency injection. The REPL should make this workflow frictionless: define handler, run computation, see results, try different handler, compare.

- **Actors are persistent objects.** Unlike most REPL values, actors have lifecycle. The REPL must respect this — showing that actors survive across lines, that they accumulate state, that they can crash and be restarted. The actor dashboard makes the REPL feel like a control room, not a calculator.

- **The compiler is always running.** Type and effect information is available before execution. `:type`, `:effects`, `:handlers` are all zero-cost queries over the compiler's existing knowledge. The REPL should feel like the compiler is your pair programmer.

- **Degrade gracefully.** Without colour: plain text with `effects: [...]`. Without TUI: ASCII tables. Without MCP: all commands still work manually. Without actors: all non-actor features still work. Every feature is an additive layer, not a dependency.

- **Exploration should become production.** Everything developed at the REPL — handler strategies, mock handlers, actor configurations, type definitions — should export cleanly to `.kea` source files. The REPL is where you discover; source files are where you persist.

---

## 17. Implementation Notes

### 17.1 Crate Stack

| Need | Crate | Notes |
|---|---|---|
| Terminal input | `rustyline` | Vi/emacs mode, syntax highlighting, multi-line |
| Syntax highlighting | Kea lexer (built-in) | Token → ANSI colour mapping |
| JIT compilation | `cranelift` | Same backend as `kea build`, JIT mode |
| TUI overlays | `ratatui` + `crossterm` | Actor dashboard, `:explore` |
| MCP server | Adapted from `rill-mcp` | Same tool surface, Kea semantics |
| History | `dirs` + filesystem | `~/.local/share/kea/history` |

### 17.2 Rustyline Integration

The `Validator` trait handles multi-line continuation:

```rust
impl Validator for KeaHelper {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> Result<ValidationResult> {
        let input = ctx.input();
        if needs_continuation(input) {
            Ok(ValidationResult::Incomplete)
        } else {
            Ok(ValidationResult::Valid(None))
        }
    }
}
```

`needs_continuation` checks for:
- Unclosed delimiters (`(`, `[`, `{`)
- Trailing block-introducing keywords
- Current indent level > 0 without blank-line termination
- Trailing operators

The `Highlighter` trait maps Kea tokens to ANSI colours using the lexer.

The `Completer` trait offers completions from the type environment: binding names, type names, effect names, method names (context-dependent on the receiver type).

### 17.3 Actor Runtime in the REPL

The REPL runs a tokio runtime. Actors are spawned onto this runtime. The REPL's main loop uses `tokio::select!` to multiplex terminal input with actor notifications:

```rust
loop {
    tokio::select! {
        line = editor.readline("kea> ") => handle_input(line),
        notification = actor_rx.recv() => display_notification(notification),
    }
}
```

Actor crashes, supervisor restarts, and lifecycle events appear as notifications between REPL prompts:

```
kea> Send.tell(buggy_actor, BadMessage)
: ()

-- Actor #7 (BuggyActor) crashed: panic "unexpected message"
-- Supervisor #4 restarting #7 (attempt 2/5)
-- Actor #7 (BuggyActor) restarted

kea>
```

### 17.4 JIT vs AOT

The REPL uses Cranelift in JIT mode. Each REPL input is compiled to a function, JIT-compiled, and called. The compiled code is kept in memory for the session's duration (since bindings may reference it).

`kea build` uses Cranelift in AOT mode. Same IR, same optimisation passes, different final step (emit object file vs call function pointer).

The REPL's JIT compilation means expressions run at native speed — not interpreted. Handler dispatch, pattern matching, actor messaging — all compiled.

### 17.5 Transfer from Rill

| Component | Transfer | Notes |
|---|---|---|
| Rustyline integration | Direct | Helper, Completer, Highlighter, Validator patterns identical |
| CLI structure (clap) | Adapt | Same subcommands with Kea keywords |
| REPL main loop | Adapt | Add effect display, handler handling |
| Input classification | Rewrite | Different keywords (struct not record, effect not frame) |
| Diagnostic rendering (ariadne) | Direct | Same crate, same patterns |
| History management | Direct | Same approach |
| Actor lifecycle | Adapt | Same tokio runtime + ordered shutdown pattern |
| MCP server | Adapt | Same tool surface, different type system backend |
| `:type`, `:env` | Adapt | Add effect information |
| `:doc` / `:trace` | Adapt | Add effect-specific queries |

---

## 18. What This Doesn't Cover

This document describes the REPL for the Kea language as specified in KERNEL v4. It does not cover:

- **IDE integration beyond LSP.** The LSP server (adapted from rill-lsp) provides editor features. The REPL is a standalone interactive environment.
- **Notebook-style interfaces.** A Jupyter kernel for Kea is a natural extension but is out of scope for the initial REPL. The MCP server provides the substrate for building one.
- **Distributed actor debugging.** The REPL's actor dashboard shows local actors. Distributed debugging (across nodes) is a future concern for the actor library.
- **Profiling.** `:bench` provides microbenchmarking. Full profiling (CPU, memory, effect dispatch overhead) is a separate tool.
- **Package management.** `kea install`, `kea update`, `kea remove` are CLI commands, not REPL commands. The REPL loads packages from `kea.toml` at startup.
