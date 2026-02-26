# Universal Dot Notation

Kea uses dot calls as the default way to compose code.

The goal is simple:
- One readable call style
- Effect signatures visible at each step
- No pipe operator needed

---

## Why This Matters

In many languages, call style splinters:
- methods for some APIs
- free functions for others
- pipes/chains/macros to glue them together

Kea keeps a single surface:

```kea
users
  .filter(|u| -> u.active)
  .map(|u| -> u.name)
  .sort()
  .take(10)
```

This is left-to-right and type-checked with normal function dispatch rules.

---

## The Four Call Forms

### 1) Unqualified method call (default)

```kea
value.method(args)
```

Use this for most code.

### 2) Prefix call (explicit module/type call)

```kea
Module.function(args)
```

Use for constructors or explicit namespaced calls.

### 3) Qualified method call (disambiguation)

```kea
value.Trait::method(args)
value.Module::function(args)
```

Use when unqualified dispatch is ambiguous or you want a specific namespace.

### 4) Receiver placement with `$`

```kea
text.String::replace("old", $, "new")
```

Use when receiver is not the first positional parameter.

---

## Resolution Rules You Can Rely On

For `value.method(args)`:
1. Inherent methods on the value's nominal type
2. In-scope trait methods
3. Error if none
4. Error if multiple trait matches

Important: inherent methods win over trait methods.

If you need the trait version explicitly:

```kea
value.SomeTrait::method()
```

---

## Field vs Method Is Explicit

- `value.name` means field access
- `value.name()` means method call

No ambiguity at parse time.

---

## Why There Is No Pipe Operator

You already get pipeline readability through dot-chaining, and each step keeps normal dispatch and effect tracking.

Instead of:

```text
x |> f |> g
```

Kea favors:

```kea
x.f().g()
```

or explicit namespaced call when needed:

```kea
x.Module::f().Module::g()
```

---

## Before/After Migration Examples

### Pipeline-heavy style

Before:

```text
users |> filter(active) |> map(name) |> sort |> take(10)
```

After:

```kea
users.filter(active).map(name).sort().take(10)
```

### Free-function style

Before:

```text
replace("old", text, "new")
```

After (receiver in middle parameter position):

```kea
text.String::replace("old", $, "new")
```

### Ambiguous method name

Before:

```text
render(widget)   # which render?
```

After:

```kea
widget.Component::render()
```

---

## Practical Style Guide

- Default to `x.method(...)`
- Use `Module.function(...)` when you want explicit constructor/static-style calls
- Use `::` only when needed for disambiguation
- Use `$` sparingly; frequent `$` usually means parameter order should be improved

---

## Quick Migration Notes

If you come from:

- **Elixir/F#/OCaml pipelines**: dot chains replace most pipe usage
- **TypeScript/Java/C#**: method style feels familiar; `::` is explicit escape hatch
- **Go**: think "explicit receiver placement and namespace calls", but in expression form

Opinionated rule: if you feel tempted to reintroduce pipes, your API surface probably needs better method naming or receiver parameter ordering.

---

## One-Line Summary

Universal dot notation gives Kea one consistent, readable, type-checked way to write pipelines without a pipe operator.
