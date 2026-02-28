# URGENT: Kea Syntax — Do NOT Use Rill Syntax

**The parser currently accepts Rill syntax, but KERNEL.md is the source of truth.**
When writing `.kea` code, you MUST use KERNEL syntax, not what the parser happens to accept from Rill.

## Correct Kea syntax (KERNEL.md)

| Construct | Kea (correct) | Rill (wrong) |
|-----------|--------------|--------------|
| Type definition | `struct Point` | `record Point` |
| Functional update | `p~{ x: 3.0 }` | `{ ..p, x: 3.0 }` or `Point { ..p, x: 3.0 }` |
| Tuple literal | `(1, 2, 3)` | `#(1, 2, 3)` |
| Tuple pattern | `(a, b)` | `#(a, b)` |
| Map literal | `%{ "key" => value }` | n/a |
| Anonymous record | `#{ x: 1, y: 2 }` | same |
| List literal | `[1, 2, 3]` | same |
| Struct literal | `Point { x: 1.0, y: 2.0 }` | same |

## Key rules

1. **`struct` not `record`** — Kea uses `struct` for product types (KERNEL §2)
2. **`~` not `..`** — Functional update is `base~{ field: value }` (KERNEL §2.3)
3. **`()` not `#()`** — Tuples are `(a, b)`, grouping is `(expr)`, unit is `()` (KERNEL §1.5)
4. **`%{}` for maps** — Map literals are `%{ key => value }` (KERNEL §1.5.1)

## Why this matters

The parser was cannibalized from Rill and hasn't been migrated yet. It accepts
both syntaxes. But all new `.kea` code must use KERNEL syntax so it doesn't
need to be rewritten when the parser migration lands. See
`BRIEFS/todo/syntax-migration-rill-to-kea.md` for the full migration plan.
