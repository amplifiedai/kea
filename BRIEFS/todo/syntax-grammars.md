# Brief: Tree-sitter and TextMate Grammars

**Status:** ready
**Priority:** v1 (parallel track)
**Depends on:** 0a (done — syntax is stable)
**Blocks:** Neovim plugin, Helix config, VS Code extension, GitHub syntax highlighting
**Cannibalise:** `/Users/chris/Projects/rill/tree-sitter-rill/` (grammar.js, queries, editor configs, design brief)

## Motivation

The stdlib is growing. Algorithm gallery entries are coming. Every `.kea`
file in the repo, every code block in docs, every snippet on GitHub —
all render as plain text right now. Syntax highlighting is the single
highest-leverage DX improvement we can ship, and it has zero compiler
dependencies.

Two artifacts, two consumer ecosystems:

1. **Tree-sitter grammar** — Neovim, Zed, Helix, Emacs. Structural
   parsing, incremental re-parse, code navigation, text objects.
2. **TextMate grammar** — VS Code, GitHub (via Linguist), Sublime,
   TextMate. Regex-based `.tmLanguage.json`. This is what makes `.kea`
   files render with colour on github.com.

Both encode the same language surface. Build together, test against the
same corpus.

## Deliverables

```
tree-sitter-kea/
  grammar.js              -- tree-sitter grammar definition
  src/                    -- generated C parser (tree-sitter generate)
  queries/
    highlights.scm        -- syntax highlighting
    indents.scm           -- auto-indentation rules
    folds.scm             -- code folding regions
    locals.scm            -- local variable scoping
  test/corpus/            -- tree-sitter test cases
  package.json            -- npm metadata (tree-sitter convention)
  bindings/               -- node + rust bindings

editors/
  nvim/                   -- Neovim plugin (tree-sitter queries + ftdetect)
  helix/languages.toml    -- Helix language config
  vscode/
    syntaxes/kea.tmLanguage.json   -- TextMate grammar
    language-configuration.json    -- bracket matching, comment toggling
    package.json                   -- VS Code extension manifest
```

## Complete Syntax Inventory

Derived from `kea-syntax` (lexer.rs, parser.rs, token.rs) and
`kea-ast` (lib.rs). This is what the grammars must cover.

### Keywords

```
let  fn  pub  if  else  case  true  false  None
type  trait  impl  where  use  test
handle  resume  effect  fail  catch
and  or  not
while  for  in
```

### Annotations

```
@tailrec   @intrinsic   @unsafe   @unboxed   @derive
```

### Operators (by precedence, lowest to highest)

| Precedence | Operators | Notes |
|------------|-----------|-------|
| 1 | `or` | Logical or |
| 3 | `and` | Logical and |
| 5 | `==` `!=` | Equality |
| 7 | `<` `<=` `>` `>=` | Comparison |
| 9 | `+` `-` | Additive |
| 11 | `*` `/` `%` | Multiplicative |
| 13 | `-` (prefix), `not` | Unary |
| 15 | `.` `(` `?` | Postfix (method call, call, try) |

### Delimiters and Punctuation

```
(  )       -- grouping, params, call args
[  ]       -- effect rows in type annotations
,          -- separator
.          -- field/method access, qualified names
:          -- type annotations
=          -- binding
->         -- pure function arrow, case arm, return type
-[...]>    -- effectful function arrow (effect row between brackets)
?          -- try operator (postfix, Fail sugar)
$          -- receiver placeholder in method chains
|          -- lambda param delimiter
```

### Identifiers

- **Lowercase** (`[a-z_][a-zA-Z0-9_]*`) — variables, functions, fields
- **Uppercase** (`[A-Z][a-zA-Z0-9_]*`) — types, constructors, modules,
  effects, traits (`Some`, `IO`, `State`, `List`)

### Literals

- **Integer:** `42`, `-7`, `0xFF`, `0b1010`, `0o77`, `1_000_000`
- **Float:** `3.14`, `-0.5`, `1.0e10`
- **String:** `"hello"`, `"line\n"` (escape sequences)
- **Bool:** `true`, `false`
- **Unit:** `()`

### Doc Comments

```
--| This is a doc comment.
--|
--|   example_call()   -- => expected
```

`--|` prefix. Blank `--|` separates description from examples.
Regular comments: `-- comment`.

## Effect-Aware Highlighting — Design

This is where Kea's grammar diverges from every other ML-family
language. The effect system is the language's defining feature, and
syntax highlighting should make effect information **visually
immediate**. A reader scanning code should be able to distinguish
pure from effectful functions at a glance.

### Principle: effects are a distinct visual layer

Most languages have two visual layers: structure (keywords, control
flow) and data (types, literals, strings). Kea has a third: **effects**.
The grammar should assign effect-related syntax to capture names that
let colour themes give effects their own colour.

### Capture name strategy

Use tree-sitter's standard capture hierarchy with effect-specific
extensions. Theme authors can then choose to colour effects distinctly
or let them fall back to their parent category.

```scheme
; === EFFECT DECLARATIONS ===
; `effect IO` / `effect Fail E` — the declaration keyword
(effect_declaration "effect" @keyword.effect)
; The effect name itself
(effect_declaration name: (upper_identifier) @type.effect)
; Type params on effects: `effect Fail E` — the E
(effect_declaration type_param: (identifier) @variable.type)

; === EFFECT ARROWS ===
; Pure arrow: ->
(pure_arrow) @operator
; Effectful arrow: -[IO, State s]>
; The brackets and dash-angle are punctuation
(effect_arrow "[" @punctuation.bracket.effect)
(effect_arrow "]" @punctuation.bracket.effect)
(effect_arrow "-" @punctuation.bracket.effect)
(effect_arrow ">" @punctuation.bracket.effect)
; Effect names inside the row: IO, State, Fail
(effect_row (upper_identifier) @type.effect)

; === HANDLE BLOCKS ===
; `handle` keyword — control flow that delimits effect scope
(handle_expression "handle" @keyword.effect)
; `then` keyword after handle block
(handle_expression "then" @keyword.effect)
; Operation clause: `State.get(s) -> resume ...`
; The Effect.operation pattern on the left of ->
(operation_clause effect: (upper_identifier) @type.effect)
(operation_clause operation: (identifier) @function.effect)
; `resume` — continuation keyword, visually special
(resume_expression "resume" @keyword.effect)

; === FAIL SUGAR ===
; `fail` keyword — raises Fail effect
(fail_expression "fail" @keyword.effect)
; `?` try operator — propagates Fail
(try_expression "?" @operator.effect)
; `catch` — Fail handler sugar
(catch_expression "catch" @keyword.effect)

; === EFFECT OPERATIONS IN CALLS ===
; `IO.stdout(msg)` — when calling an effect operation
; The module part (IO) is already @type via upper_identifier
; The operation (stdout) gets @function.call
; No special treatment needed — module-qualified calls already work

; === TRAIT vs EFFECT distinction ===
; Both use upper_identifier, but declarations differ:
(trait_declaration "trait" @keyword)
(trait_declaration name: (upper_identifier) @type)
(effect_declaration "effect" @keyword.effect)
(effect_declaration name: (upper_identifier) @type.effect)
```

### What this enables in colour themes

With these captures, a theme can:

1. **Colour all effect-related syntax one colour** (e.g. purple for
   effects, blue for types, orange for keywords). Set `@keyword.effect`,
   `@type.effect`, `@operator.effect` all to purple. Now `handle`,
   `resume`, `fail`, `catch`, `-[IO]>`, and `effect IO` all visually
   cohere as "the effect layer."

2. **Colour effects like types** by not overriding `.effect` captures.
   They fall back to their parent (`@keyword`, `@type`, `@operator`).
   This is the safe default for themes that don't know about Kea.

3. **Make effectful arrows visually distinct from pure arrows.** A theme
   could make `->` dim/gray and `-[...]>` bright, so effectful function
   signatures stand out during code review.

4. **Make `resume` as prominent as `return`.** Both are control flow
   that determines what value reaches the caller. `resume` is arguably
   more important — it's a continuation.

### TextMate grammar mapping

TextMate uses scope names, not tree-sitter captures. Map as:

| Tree-sitter capture | TextMate scope |
|---------------------|---------------|
| `@keyword.effect` | `keyword.control.effect.kea` |
| `@type.effect` | `entity.name.type.effect.kea` |
| `@operator.effect` | `keyword.operator.effect.kea` |
| `@punctuation.bracket.effect` | `punctuation.definition.effect.kea` |
| `@function.effect` | `entity.name.function.effect.kea` |

### Visual examples

What highlighting achieves (using `[brackets]` for effect colour,
**bold** for keywords, *italic* for types):

```
**effect** [IO]
  **fn** stdout(msg: *String*) -[[IO]]> *Unit*

**fn** greet(name: *String*) -[[IO]]> *Unit*
  [IO].stdout("hello " ++ name)

**fn** pure_add(x: *Int*, y: *Int*) -> *Int*
  x + y

**handle** program()
  [IO].stdout(msg) -> [resume] ()
  [IO].stderr(msg) -> [resume] ()
**then** result ->
  result
```

The visual contrast between `->` (pure) and `-[[IO]]>` (effectful)
is the key insight. At a glance, you can see which functions touch
the world.

## Implementation Plan

### Step 1: Tree-sitter grammar (~200–400 lines of grammar.js)

Cannibalise `tree-sitter-rill/grammar.js` as the starting point.

**Remove:** `frame`, `sql`, `html`, `markdown`, `spawn`, `stream`,
`yield`, `yield_from`, `import` (Kea uses `use`), braces for blocks,
pipe operator `|>`, map literals `%{`, anonymous records `#{}`.

**Add:**
- `effect` declarations with operations
- `handle` expressions with operation clauses
- `resume` expression
- Effect arrows `-[effects]>`
- `fail`, `catch`, `?` (try) as effect sugar
- `test "name"` blocks
- `use` imports (replacing `import`)
- `@annotation` syntax
- Indentation-sensitive blocks (the big structural change)
- `--|` doc comments
- `while` loops
- Hex/binary/octal literals with underscore separators

**Indentation handling:** Kea is indentation-sensitive, which
tree-sitter traditionally struggles with. Two approaches:

1. **External scanner** (C code) that tracks indent/dedent and
   emits virtual INDENT/DEDENT tokens. This is what tree-sitter-python
   does. More complex but structurally correct.
2. **Flat grammar with indentation queries** — parse blocks as
   sequences without explicit indent tracking, use `indents.scm`
   for editor behaviour. Simpler, works well enough for highlighting.

Recommend approach 2 for the initial grammar. Highlighting doesn't
need perfect block structure — it needs to colour tokens correctly.
Approach 1 can be added later if structural editing / code navigation
needs it.

### Step 2: Highlight queries (~80 lines)

Write `highlights.scm` using the capture strategy above. Test against:
- Every stdlib module (16 files — effects, traits, pure functions)
- Handler test files (clock_tests.kea, rand_tests.kea)
- Effect declarations, handle blocks, resume, fail, catch

### Step 3: TextMate grammar (~200–300 lines JSON)

Regex-based, targeting VS Code + GitHub Linguist. Priority patterns:

1. Comments (`--`, `--|`)
2. Strings (with escapes)
3. Keywords (two groups: regular + effect-related)
4. Effect arrows `-[...]>` (regex: `-\[.*?\]>`)
5. Annotations (`@word`)
6. Numbers (int, float, hex, binary, octal)
7. Operators
8. Identifiers (upper = type/effect/constructor, lower = variable/function)

**Structure the TextMate grammar for Linguist extraction.** GitHub
requires a standalone repo containing the `.tmLanguage.json` for
Linguist to pull from. The grammar should be self-contained in
`editors/vscode/syntaxes/kea.tmLanguage.json` with `scopeName:
source.kea` — ready to be published to its own repo (e.g.
`kea-textmate-grammar`) when we submit the Linguist PR.

The `.kea` extension is currently used by KEA Image (HDF5-based
GIS raster format from kealib.org) — not a programming language,
so no grammar conflict, but Linguist will need a content-based
disambiguation heuristic. Include a first-line or keyword pattern
that distinguishes Kea source from binary HDF5 files (e.g.
presence of `fn `, `effect `, `type `, `use `, or `--|`).

### Step 4: Editor configs

- **Neovim:** ftdetect (`*.kea`), queries symlinked from tree-sitter-kea
- **Helix:** `languages.toml` entry
- **VS Code:** minimal extension with TextMate grammar + language config

### Step 5: Test corpus

Tree-sitter test files in `test/corpus/`:
- `literals.txt` — all literal forms
- `functions.txt` — fn declarations, lambdas, annotations
- `types.txt` — type annotations, arrows, effect rows
- `effects.txt` — effect declarations, handle, resume, fail, catch
- `control_flow.txt` — if/else, case, while
- `modules.txt` — use declarations, qualified names

Test every stdlib file as a parse-without-error check.

## Cannibalization Guide

**From `tree-sitter-rill/`:**

| Rill artifact | Kea action |
|--------------|------------|
| `grammar.js` (27KB) | Copy, strip Rill-specific (frame/sql/html/spawn), add effect syntax |
| `queries/highlights.scm` | Copy, remove Rill captures (atom, frame, sql), add effect captures |
| `queries/indents.scm` | Adapt for indent-sensitive (simpler — no braces to match) |
| `queries/folds.scm` | Adapt fold points for indent blocks |
| `queries/locals.scm` | Copy mostly as-is (scoping rules similar) |
| `editors/nvim/` | Copy, rename rill → kea |
| `editors/helix/` | Copy, rename |
| `BRIEFS/done/tree-sitter-grammar.md` | Reference for design decisions, don't copy |

**From Rill's grammar, keep:**
- Expression precedence climbing
- String literal handling (escapes)
- Pattern matching (constructor, variable, wildcard)
- Trait declarations and impl blocks
- Binary/unary operator structure
- Comment handling

**From Rill's grammar, remove:**
- `frame` / DataFrame syntax
- `sql {}` / `html {}` / `markdown {}` embedded blocks
- `spawn` / `stream` / `yield` / `yield_from`
- Brace-delimited blocks `{ }` (Kea uses indentation)
- `import` (Kea uses `use`)
- Pipe operator `|>`
- Map literals `%{}`
- Anonymous records `#{}`
- `#(` tuple syntax

## Definition of Done

- [ ] Tree-sitter grammar parses all stdlib modules without error
- [ ] Tree-sitter grammar parses all test `.kea` files without error
- [ ] `highlights.scm` assigns distinct captures to: effect declarations,
      effect arrows, handle/resume/fail/catch, pure vs effectful arrows
- [ ] TextMate grammar highlights `.kea` files in VS Code
- [ ] Neovim config works: `*.kea` files get highlighting via tree-sitter
- [ ] Helix config works: `*.kea` files get highlighting
- [ ] Effect-related syntax is visually distinguishable from regular
      keywords/types in at least one theme configuration
- [ ] Test corpus covers: literals, functions, types, effects, handlers,
      control flow, modules, doc comments
- [ ] TextMate grammar is self-contained and extractable to a standalone
      repo for GitHub Linguist submission
