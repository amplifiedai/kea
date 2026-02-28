# Brief: Const Fields

**Status:** active
**Priority:** v1
**Depends on:** 0d (codegen working)
**Blocks:** stdlib-bootstrap (module constants like `Math.pi`, `Int.max_value`)

## Summary

Add `const` fields to structs per KERNEL §2.9. Const fields are
compile-time-known named values with no runtime struct layout
representation. Module structs (singletons) may have const fields
but not runtime fields — this is how Kea gets module-level constants.

## Scope

Phase 0 implements the strict subset: literals, const references,
constructors, primitive ops. The semantic contract (pure = eligible)
is established but function-call const evaluation is deferred.

## Implementation

### 1. Parser

Add `const` as a declaration form inside struct blocks:

```
const name: Type = expr
```

In `parse_struct_body` (or equivalent), when the parser sees `const`
keyword, parse: ident, `:`, type annotation, `=`, expression.

AST node: add `ConstField` variant to struct member declarations.

### 2. Type checker

- Validate the initializer is a pure expression (`->`, no effects)
- Validate the initializer type matches the declared type
- For the strict subset: reject function calls in const position
  with a clear error ("const evaluation of function calls is not
  yet supported")
- Register const fields in the type environment so `Type.name`
  resolves during qualified access
- Module structs: reject runtime fields (only const + fn allowed)

### 3. Const evaluation

Evaluate strict-subset const expressions at compile time:
- Literals: trivial
- Const refs: look up already-evaluated const
- Constructors: build the value from const args
- Primitive ops (`+`, `*`, etc.): fold

Order: topological sort of const dependencies within a struct.
Circular const references are a compile error.

### 4. Codegen

- `@unboxed` types: inline as immediate operands
- Heap types: emit in static read-only data section with immortal
  refcount (sentinel value, e.g. `isize::MAX`). Skip retain/release
  on const references.
- Qualified access (`Math.pi`): load from static data or inline
  the immediate, depending on type

### 5. Const patterns

- In pattern compilation, when a pattern is `Type.name` and `name`
  resolves to a const field: inline the const value, emit equality
  check
- Require the type to implement `Eq`
- Exhaustiveness: const patterns are not exhaustive (always need
  a wildcard or full enum coverage alongside them)

### 6. Evaluator (`kea-eval`)

Add const field resolution to the tree-walking evaluator. Evaluate
const initializers once at module load time, cache the result.

## Tests

```kea
-- Basic const field on module struct
struct Math
  const pi: Float = 3.14159265358979
  const tau: Float = 2.0 * pi

fn main() -> Float
  Math.tau
-- expected: 6.28318530717958

-- Const field on data struct
struct Color
  r: Int
  g: Int
  b: Int
  const red: Color = Color { r: 255, g: 0, b: 0 }
  const black: Color = Color { r: 0, g: 0, b: 0 }

fn main() -> Int
  Color.red.r
-- expected: 255

-- Const in pattern position
fn describe(_ c: Color) -> String
  case c
    Color.red -> "danger"
    Color.black -> "void"
    _ -> "other"

-- Module struct rejects runtime fields
struct Bad
  x: Int              -- ERROR: module structs cannot have runtime fields
  const y: Int = 42

-- Unsupported const expression (clear error)
struct Util
  const root2: Float = Float.sqrt(2.0)  -- ERROR: const evaluation of function calls is not yet supported

-- Circular const reference
struct Loop
  const a: Int = b + 1  -- ERROR: circular const dependency
  const b: Int = a + 1
```

## Validation

```
mise run check-full
PKG=kea-syntax mise run test-pkg
PKG=kea-infer mise run test-pkg
PKG=kea-mir mise run test-pkg
PKG=kea mise run test-pkg
```

## Progress
- 2026-02-28 15:54: Parser/AST slice landed locally: added `const` keyword token + lexer support, struct-body `const name: Type = expr` parsing, `RecordDef.const_fields` + `ConstField` AST node, parser regression tests, and downstream `RecordDef` constructor updates in `kea-infer`, `kea-mir`, and benchmark helpers. Validation run: `mise run check`, `PKG=kea-syntax mise run test-pkg`, `PKG=kea-infer mise run test-pkg`, `PKG=kea-mir mise run test-pkg`.
- **Next:** implement type-checker const-field registration + purity/type validation, then wire const evaluation/lowering.
