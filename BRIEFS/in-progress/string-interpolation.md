# Brief: String Interpolation

**Status:** active
**Priority:** v1-critical
**Depends on:** 0a (parser), Show trait (stdlib)
**Blocks:** self-hosting (error messages are half the compiler)

## Summary

Implement KERNEL §1.6 string interpolation: `"Hello, {expr}"`.
The expression inside `{}` must have a type that implements `Show`.
The compiler desugars to `Show.show()` calls and string concatenation.

## Syntax

```kea
let name = "world"
let x = 42
"Hello, {name}"           -- "Hello, world"
"x is {x}"                -- "x is 42"
"sum is {x + 1}"          -- "sum is 43"
"point is ({p.x}, {p.y})" -- nested field access
"{x}"                      -- just show x
```

Braces `{}` delimit interpolation. Literal `{` is escaped as `{{`.

## Implementation

### 1. Lexer

When lexing a string literal and encountering `{` (not `{{`):
- Emit the string-so-far as a `StringFragment` token
- Switch to expression-lexing mode (track brace depth)
- On matching `}`, emit `InterpolationEnd`, resume string lexing
- Repeat until closing `"`

Token stream for `"a is {x + 1}!"`:
```
StringStart, StringFragment("a is "), InterpolationStart,
Ident("x"), Plus, Int(1), InterpolationEnd,
StringFragment("!"), StringEnd
```

Alternative (simpler): desugar entirely in the parser. Lex the
whole string as a raw string, then have the parser re-scan for
`{...}` and parse the interpolated expressions. This avoids
lexer mode-switching but means the parser needs to handle raw
string internals.

Either approach works. Lexer-level is cleaner for error reporting
(mismatched braces get span-accurate diagnostics).

### 2. Parser

Produce an `Expr::StringInterpolation` AST node containing a
list of parts: `Vec<StringPart>` where:

```rust
enum StringPart {
    Literal(String),
    Expr(Expr),
}
```

### 3. Type checker

Each interpolated expression must satisfy `Show`. Emit a trait
obligation for `Show` on each expression's inferred type.
Primitive types (Int, Float, Bool, String) satisfy this implicitly.

The overall expression has type `String`.

### 4. Lowering (HIR/MIR)

Desugar to a chain of `Show.show()` calls and string concatenation:

```
"a is {x + 1}!" → String.concat("a is ", Show.show(x + 1), "!")
```

Or more precisely, lower to a series of `show` calls joined by
the string concat intrinsic.

### 5. Codegen

No special codegen needed — the desugared form uses existing
function call and string concat machinery.

## Tests

```kea
fn main() -> String
  let x = 42
  "x is {x}"
-- expected: "x is 42"

fn main() -> String
  "sum is {1 + 2}"
-- expected: "sum is 3"

fn main() -> String
  let name = "world"
  "Hello, {name}!"
-- expected: "Hello, world!"

fn main() -> String
  "literal braces: {{not interpolated}}"
-- expected: "literal braces: {not interpolated}"

-- ERROR: type Foo does not implement Show
struct Foo
  x: Int
fn main() -> String
  let f = Foo { x: 1 }
  "{f}"
```

## Validation

```
mise run check-full
PKG=kea-syntax mise run test-pkg
PKG=kea mise run test-pkg
```
