# Kea Call Syntax Matrix

Formal specification of all call forms, their desugaring, and
when each should be used.

---

## Call Forms

There are exactly four syntactic forms for calling functions.
Two are primary (used in most code). Two are for special cases.

### Primary Forms

**1. Method call (unqualified)**

```
expr.method(args)
```

Desugars to: `resolve(method, typeof(expr))(expr, args)`

Resolution:
1. Check inherent methods on the nominal type of `expr`.
2. Check trait methods from in-scope traits implemented for `typeof(expr)`.
3. If exactly one match: call it with `expr` as first `_` param.
4. If zero matches: compile error.
5. If multiple matches: compile error with fix suggestions showing
   qualified forms.

This is the canonical style. 95% of code uses this form.

```kea
users.filter(|u| -> u.active).map(|u| -> u.name).sort().take(10)
```

**2. Prefix call (qualified)**

```
Module.function(args)
```

No desugaring. Direct call to a specific function on a specific
type/module. Used for constructors, static methods, and when the
receiver-as-first-argument pattern doesn't apply.

```kea
let n = Int.parse("42")
let total = Enum.sum(scores)
let p = Point.origin()
```

### Special Forms

**3. Qualified method call (qualified dispatch)**

```
expr.Qualifier::method(args)
```

Desugars to: `Qualifier.method(expr, args)`

`Qualifier` is a trait name or module name. Used only when
unqualified dispatch (Form 1) is ambiguous.

```kea
-- Trait qualification (two traits define `show`):
value.Show::show()
value.Debug::show()

-- Module qualification (generic function on a specific module):
users.Enum::filter(|u| -> u.active)
```

**Style rule:** Never use `::` when unqualified dispatch works.
Linters should warn on unnecessary qualification.

**4. Receiver placement ($)**

```
expr.method(a, $, b)
expr.Qualifier::method(a, $, b)
```

Desugars to: `method(a, expr, b)` or `Qualifier.method(a, expr, b)`

`$` marks where the receiver goes when it's NOT the first positional
parameter. Exactly one `$` per call. If `$` is absent, receiver
fills the first `_` positional parameter.

```kea
-- String.replace(target, input, replacement) — input is 2nd param
text.String::replace("old", $, "new")

-- Json.decode(input, schema) — input is 1st param, no $ needed
body.Json::decode($, User)
```

**Style rule:** `$` should be rare. If you're using `$` frequently,
the API's parameter order should be reconsidered.

---

## Actor Operators

Actor communication uses ordinary method calls via the `Send`
effect defined in the actor library (§19):

```
Send.tell(ref, msg)     Tell: fire-and-forget. Requires msg : M ().
Send.ask(ref, msg)      Ask: request-response. Returns T from M T.
```

Both are standard effect operations with the `Send` effect.
No special operators are needed.

---

## Resolution Algorithm

### Field vs Method

`expr.name` (no parens) is **always** field access.
`expr.name(args)` (with parens) is **always** a method call.

A field and a zero-arg method may coexist with the same name on
the same type. The grammar distinguishes them. However, this is
a lint warning — it confuses humans even if unambiguous to the
compiler.

### Unqualified Method Call: `expr.method(args)`

```
1. Let T = typeof(expr)

2. INHERENT SEARCH:
   If T is a nominal type (struct or enum), search for
   `method` in T's struct block.
   If found → USE IT. Inherent always wins. Stop here.

3. TRAIT SEARCH (only if no inherent match):
   For each trait Tr in scope (prelude + explicit use):
     If Tr has method `method` AND T satisfies Tr's bounds:
       Add Tr.method to candidate set.

4. DECIDE:
   |candidates| == 0  → error: no method `method` on type T
   |candidates| == 1  → desugar to candidate(expr, args)
   |candidates| > 1   → error: ambiguous — multiple traits
                         provide `method` for type T.
                         Suggest: expr.Trait1::method() or
                                  expr.Trait2::method()
```

**Key rule: inherent wins over trait.** If a struct has an inherent
method `render` and an in-scope trait also provides `render`, the
inherent method is called silently. No ambiguity. To call the trait
version, use qualified dispatch: `expr.Component::render()`.

Only trait-vs-trait collisions produce ambiguity errors. Inherent
methods never collide with anything.

**Scope of unqualified dot:** Inherent methods + in-scope trait
methods only. Module functions are NOT part of unqualified dot
resolution. `users.Enum::filter(f)` requires qualification.
`users.filter(f)` works only if `filter` is inherent on `List`
or on a trait in scope.

### Qualified Method Call: `expr.Qual::method(args)`

```
1. Check Qual is a trait name or struct/module name in scope.
2. If trait: verify typeof(expr) implements Qual.
   If module: verify Qual.method exists and typeof(expr) matches
   the receiver slot (first _ param, or $ position).
3. Desugar to Qual.method(expr, args).
   (Or Qual.method(a, expr, b) if $ is present.)
```

### Receiver Placement Rules

```
1. If $ appears in args:
   - Receiver fills the $ position.
   - Exactly one $ allowed per call.

2. If no $ in args:
   - Receiver fills the first parameter marked _ (positional).
   - If no _ parameter exists: compile error:
     "cannot use method syntax — no positional parameter
     for receiver"

3. Labeled parameters are never receiver candidates.
```

---

## What Is NOT Allowed

- **No `|>` pipe operator.** Use method syntax instead.

- **No implicit search beyond scope.** `.` does not search all
  installed packages for matching functions. Only inherent methods
  and in-scope traits are considered. Module functions require
  either prefix form (`Module.f(x)`) or qualified dot
  (`x.Module::f()`).

- **No multiple `$` in one call.** `a.f($, $)` is a compile error.

- **No top-level bare function definitions.** `fn foo() -> Int` at
  module level is a compile error. Functions must be inside a struct
  block.

- **Bare function CALLS on function-typed values ARE allowed.**
  If `f` is a local binding, parameter, or field with a function
  type, `f(args)` is legal. This is value application, not a
  function definition.

```kea
let f = |x| -> x * 2
f(10)                    -- legal: f is a function-typed value

let handler = router.get("/")
handler(request)         -- legal: handler is a function-typed value
```

---

## Diagnostic Quality

The compiler should produce high-quality diagnostics for method
resolution issues:

**No method found:**
```
error: no method `frobnicate` on type `User`
  --> src/app.kea:42:8
   |
42 |   user.frobnicate()
   |        ^^^^^^^^^^^ method not found
   |
   = help: did you mean `fabricate`? (defined on User)
   = help: trait `Frobbable` has method `frobnicate`
           add `use Frobbable` to bring it into scope
```

**Ambiguous method (trait-vs-trait):**
```
error: multiple methods named `render` for type `Widget`
  --> src/app.kea:42:8
   |
42 |   widget.render()
   |          ^^^^^^ ambiguous
   |
   = candidates:
     Drawable::render (trait method from graphics)
     Component::render (trait method from kea-web)
   = help: use qualified dispatch:
     widget.Drawable::render()
     widget.Component::render()
```

**Inherent shadows trait (no error, but info available):**
```
info: inherent method `Widget.render` shadows `Component::render`
  --> src/app.kea:42:8
   |
   = help: to call the trait method instead:
     widget.Component::render()
```

**Unnecessary qualification:**
```
warning: unnecessary qualification on `Show::show`
  --> src/app.kea:42:8
   |
42 |   value.Show::show()
   |         ^^^^^^ unnecessary
   |
   = help: `show` is unambiguous for type `Point`
   = help: simplify to: value.show()
```

---

## Summary Table

| Form                        | When to use                    | Frequency |
|-----------------------------|--------------------------------|-----------|
| `x.method(args)`            | Default. Method chaining.      | ~90%      |
| `Module.function(args)`     | Constructors, static methods.  | ~8%       |
| `x.Trait::method(args)`     | Disambiguation only.           | ~1%       |
| `x.method(a, $, b)`        | Non-first receiver position.   | ~1%       |
| `Effect.operation(args)`    | Effect operations.             | Varies    |
