# keadocs generator — render contract (reference)

> **Superseded by:** `BRIEFS/todo/kea-doc-bootstrap.md` which combines this
> render contract with the implementation plan. This file is retained as
> detailed reference for the output contract. The brief is canonical.

*Specification for `kea docs`, the static documentation generator. This is the
ExDoc/rustdoc equivalent for kea. It reads source code and doc blocks, renders
HTML pages, and bundles them with the keadocs design system assets.*

*Reference material:*
- `keadocs/css/keadocs.css` — the canonical CSS bundle (all `kd-*` classes)
- `keadocs/CLASS-MAP.md` — maps reference mock class names → canonical `kd-*`
- `keadocs/preview/index.html` — component catalog (validates all components)
- `docs/DESIGN-SYSTEM.md` — visual identity specification
- `docs/spec/KERNEL.md` — language specification (declaration forms, syntax)

---

## 1. page types

The generator produces four page types. Each is a static HTML file that
references keadocs.css. All use the three-panel layout (`kd-panels`) with
a shared sidebar and a sticky nav.

### 1.1 module page

One per `.kea` file. The module page is the entry point for a module
(e.g. `io`, `list`, `http.server`). It lists every public declaration
in the module.

**URL:** `{pkg}/{version}/{module_path}/`

**Example:** `kea_http/0.3.0/http/server/`

### 1.2 effect page

One per `pub effect` declaration. Renders the full effect declaration
block, its operations, available handlers, and any doc block.

**URL:** `{pkg}/{version}/{module_path}/{EffectName}/`

**Example:** `core/0.1.0/io/IO/`

### 1.3 type page

One per `pub struct`, `pub enum`, or `pub type` alias. Renders the type
definition, fields/variants, trait implementations, and inherent methods.

**URL:** `{pkg}/{version}/{module_path}/{TypeName}/`

**Example:** `core/0.1.0/list/List/`

### 1.4 trait page

One per `pub trait` declaration. Renders the trait definition, required
and default methods, known implementations.

**URL:** `{pkg}/{version}/{module_path}/{TraitName}/`

**Example:** `core/0.1.0/eq/Eq/`

---

## 2. required sections per page type

Every page shares a common structure. The order below is the render
order in the HTML. Sections marked (if applicable) are omitted when
the data source is empty.

### 2.1 all pages

```
nav bar              kd-nav
breadcrumb           kd-breadcrumb
page header          kd-page-header
  page title         kd-page-title
  page meta          kd-page-meta (tag badge + module path + [src] link)
  page description   kd-page-desc (from module-level or item-level doc block)
```

### 2.2 module page

```
[page header]
major rule                     kd-rule--major
section: effects               kd-section-label
  for each pub effect:
    effect name + badge        kd-sidebar__link pattern
    brief (first sentence)
section: types                 kd-section-label
  for each pub struct/enum/type alias:
    type name + tag badge
    brief
section: traits                kd-section-label (if applicable)
  for each pub trait:
    trait name + tag badge
    brief
section: functions             kd-section-label
  for each pub fn (inherent methods grouped under their struct):
    function entry             kd-fn-entry
      function name            kd-fn-name + [src] link
      signature block          kd-sig (pure/effectful/polymorphic)
      doc block                kd-fn-doc
      example                  kd-example (if applicable)
footer                         kd-footer
```

### 2.3 effect page

```
[page header]
  tag: effect                  kd-page-tag--effect
effect declaration block       kd-effect-decl
  full effect definition       (all operations, syntax-highlighted)
handler panel                  kd-handler-panel (if applicable)
  lists known handlers         (name + brief + link)
section rule                   kd-rule--section
section: operations            kd-section-label
  for each operation in the effect:
    function entry             kd-fn-entry
      operation name           kd-fn-name
      signature block          kd-sig kd-sig--effectful
      doc block                kd-fn-doc
      example                  kd-example (if applicable)
footer
```

### 2.4 type page — struct

```
[page header]
  tag: struct                  kd-page-tag--struct
type definition block          kd-type-def (if fields are pub)
trait tags                     kd-trait-list (if applicable)
section: fields                kd-section-label
  for each pub field:
    field entry                kd-field (name, type, description)
section: constructors          kd-section-label (if applicable)
section: inherent methods      kd-section-label
  for each pub fn in the struct block:
    function entry             kd-fn-entry
section: trait implementations kd-section-label (if applicable)
  for each `Type as Trait`:
    trait name (linked)
    method entries
footer
```

### 2.5 type page — enum

```
[page header]
  tag: enum                    kd-page-tag--enum
type definition block          kd-type-def
section: variants              kd-section-label
  for each variant:
    variant entry              kd-variant (name, fields, description)
section: inherent methods      kd-section-label (if applicable)
section: trait implementations kd-section-label (if applicable)
footer
```

### 2.6 type page — type alias

```
[page header]
  tag: alias
type definition block          kd-type-def
  expanded definition
doc block
footer
```

### 2.7 trait page

```
[page header]
  tag: trait                   kd-page-tag--trait
trait definition block         kd-type-def (teal border)
section: required methods      kd-section-label
  for each method without a default body:
    function entry             kd-fn-entry
section: default methods       kd-section-label (if applicable)
  for each method with a default body:
    function entry
section: known implementations kd-section-label (if applicable)
  for each `Type as Trait` found in the index:
    type name (linked) + brief
footer
```

---

## 3. signature rendering rules

The signature block is the most important visual component. It appears
on every function, operation, trait method, and effect declaration.
The rendering rules are strict.

### 3.1 border color

Determined by the function's declared effect set:

| declared effects | border class | border color |
|---|---|---|
| `->` (pure, empty set) | `kd-sig` | olive (`--kd-sig-pure`) |
| `-[E1, E2, ...]>` (concrete effects) | `kd-sig kd-sig--effectful` | scarlet (`--kd-sig-effectful`) |
| `-[e]>` or `-[E, e]>` (effect variable present) | `kd-sig kd-sig--polymorphic` | teal (`--kd-sig-polymorphic`) |

The rule: if the effect annotation contains a lowercase effect variable
(`e`, `eff`, etc.), it's polymorphic. If it contains only concrete
named effects, it's effectful. If the arrow is `->`, it's pure.

### 3.2 syntax highlighting within signatures

Every token in the signature gets a `kd-syn-*` span:

| token | class | example |
|---|---|---|
| `fn`, `let`, `match`, `handle`, `effect`, `trait`, `pub` | `kd-syn-keyword` | `fn` |
| type names (starts uppercase) | `kd-syn-type` | `String`, `List`, `IO` |
| effect names in the arrow | `kd-syn-effect` | `IO` in `-[IO]>` |
| function/operation name | `kd-syn-function` | `read_file` |
| parameter names | `kd-syn-param` | `path`, `self` |
| operators, arrow brackets | `kd-syn-operator` or `kd-arrow` | `->`, `-[`, `]>` |
| string literals | `kd-syn-string` | `"hello"` |
| comments | `kd-syn-comment` | `-- a comment` |

### 3.3 type crosslinks

Every type name in a signature that refers to a documented type is
wrapped in `<a class="kd-type-link" href="...">`. The link resolves
to that type's page within the same package, or to the source package
if it's a dependency.

### 3.4 effect arrow coloring

The brackets and arrow characters (`-[`, `]>`) use class `kd-arrow`
(scarlet). Effect names inside use `kd-syn-effect`. The pure arrow
`->` uses `kd-arrow--pure` (neutral).

### 3.5 effect expand panel (optional)

When a signature has concrete effects (effectful border), the effect
arrow is wrapped in `kd-effect-trigger`. On click, an `kd-expand`
panel slides in below the signature, showing one `kd-expand__row`
per effect: the effect name (with badge-colored label) and a brief
description linking to its reference page.

This is a progressive enhancement. The page works without JS. With
JS, the expand panel appears.

### 3.6 hover thicken

On hover, the signature block border thickens from 3px to 5px
(`transition: border-left-width 0.15s ease`). This is already in the
CSS. The generator does not need to do anything special — it's a CSS
`:hover` rule.

---

## 4. data inputs

The generator reads kea source code and produces HTML. It does NOT
need a running compiler. It operates on syntactic structure and doc
blocks, augmented by optional compiler metadata when available.

### 4.1 primary inputs (always available)

**Source files.** The generator parses `.kea` files to extract:

- Module structure (file path → module name, per §11.1)
- Top-level declarations: `pub struct`, `pub enum`, `pub effect`,
  `pub trait`, `pub type`, `pub fn`
- Visibility: only `pub` items appear in docs
- `doc` blocks (inline `doc ...` and block `doc\n  ...` forms, per
  KERNEL.md §2 notation)
- Function signatures: name, parameters (with `_` label elision),
  types, return type, effect annotation
- Struct fields (with visibility)
- Enum variants (with fields and optional GADT return types)
- Effect declarations (operations)
- Trait declarations (required methods, default methods, associated
  types, supertraits)
- `impl` blocks: `Type as Trait` (for "known implementations" lists)
- Inherent methods (functions inside struct blocks with `self` param)
- Nested types (structs/enums defined inside a struct block, §2.10)
- Const fields (§2.9)
- Type parameters and `where` clauses

**Package manifest.** `kea.toml` provides:
- Package name, version, description
- Dependencies (for cross-package linking)
- Repository URL (for `[src]` links)

### 4.2 enhanced inputs (when compiler metadata is available)

These are optional. The generator works without them. When present,
they improve output quality.

**Inferred effect sets.** The compiler can export the fully-resolved
effect set for each function. This lets the generator:
- Verify declared signatures match inferred effects
- Populate effect expand panels with resolved effect provenance

**Trait implementation index.** A JSON export of all `Type as Trait`
relationships across the package (and dependencies). Enables the
"known implementations" section on trait pages and "implements" list
on type pages.

**Cross-reference index.** A JSON map of `QualifiedName → URL` for
every documented item in every dependency. Enables cross-package
type links in signatures.

### 4.3 doc block format

Doc blocks are plain text. No markdown. No special formatting syntax
beyond what kea already has.

The first sentence (terminated by `. ` or end of first line in inline
form) is the **brief**. It appears in summaries, sidebar tooltips,
search results, and module-level listings.

The full doc block appears on the item's dedicated page.

Within a doc block:
- Backtick-wrapped text (`` `like_this` ``) is rendered as inline code
- References to other items in the package are auto-linked when
  unambiguous (e.g. `List.map` becomes a crosslink)
- Code blocks indented by 2+ spaces from the doc indent level are
  rendered as `kd-example` blocks

### 4.4 what the generator does NOT do

- **No type inference.** It reads declared signatures, not inferred ones.
  Functions without signatures (closures) are not documented.
- **No evaluation.** Doc examples are rendered as-is, not executed.
- **No cross-package source reading.** Dependencies are linked via
  the cross-reference index, not by parsing their source.

---

## 5. static asset contract

The generator bundles these assets into every docs output directory.
They are the complete runtime — no external CDN, no build step.

### 5.1 CSS

```
_assets/
  keadocs.css              — the full design system bundle
```

Source of truth: `keadocs/css/keadocs.css` in the kea repo.

One file. No CSS preprocessor. No build step. The generator copies it
verbatim. Every page links it with:

```html
<link rel="stylesheet" href="/_assets/keadocs.css">
```

The CSS contains all tokens (colors, typography, spacing), all semantic
mappings, all component styles, both density modes, dark mode (both
`[data-theme]` and `prefers-color-scheme`), and print styles.

### 5.2 fonts

```
_assets/fonts/
  syne-variable.woff2      — display / headings
  literata-variable.woff2  — body text
  plex-mono-variable.woff2 — code
```

Three variable font files. The CSS references them via `@font-face`
declarations (which are NOT currently in keadocs.css — the generator
or the consuming page loads them). The font-face declarations should
be added to keadocs.css or shipped as a separate `_assets/fonts.css`.

Font loading strategy: `font-display: swap`. System fallbacks in the
CSS already cover the flash.

### 5.3 JavaScript

```
_assets/keadocs.js         — minimal, progressive enhancement only
```

Three responsibilities. Nothing more.

**Theme toggle.** Reads `localStorage('kd-theme')`, applies
`data-theme` attribute on `<html>`, toggles `○` / `●`. Falls back
to `prefers-color-scheme` when no stored preference.

**Effect expand panels.** Click handler on `kd-effect-trigger` elements
that toggles `kd-expand--visible` on the sibling `kd-expand` panel.

**Search.** Keyboard shortcut (`⌘K` / `Ctrl+K`) opens a search overlay.
Search index is a static JSON file (`_assets/search-index.json`)
generated alongside the HTML. Client-side filtering. No server
component.

The page is fully functional without JavaScript. Theme respects
`prefers-color-scheme`. Effect expand panels are hidden (signatures
still readable). Search falls back to browser find.

### 5.4 search index

```
_assets/search-index.json
```

Array of entries. Each entry:

```json
{
  "name": "List.map",
  "kind": "fn",
  "module": "list",
  "brief": "Apply a function to every element, collecting results.",
  "signature": "fn map(_ self: List A, _ f: A -[e]> B) -[e]> List B",
  "effects": ["polymorphic"],
  "url": "list/List/#map"
}
```

Kinds: `fn`, `struct`, `enum`, `effect`, `trait`, `type`, `field`,
`variant`, `operation`.

### 5.5 output directory structure

```
{pkg}/{version}/
  _assets/
    keadocs.css
    keadocs.js
    search-index.json
    fonts/
      syne-variable.woff2
      literata-variable.woff2
      plex-mono-variable.woff2
  index.html                    — package landing (module list)
  {module}/
    index.html                  — module page
    {TypeName}/
      index.html                — type page
    {EffectName}/
      index.html                — effect page
    {TraitName}/
      index.html                — trait page
```

### 5.6 HTML template

Every page is a complete, self-contained HTML document:

```html
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{page_title} — {pkg_name} {version}</title>
  <link rel="stylesheet" href="/_assets/keadocs.css">
</head>
<body class="kd-reference">
  <nav class="kd-nav"> ... </nav>
  <div class="kd-panels">
    <aside class="kd-panels__sidebar"> ... </aside>
    <main class="kd-panels__main"> ... </main>
  </div>
  <script src="/_assets/keadocs.js" defer></script>
</body>
</html>
```

Note `body.kd-reference` — all generated docs use reference density
(0.95rem / 1.6 line-height). The reading density is for kea-www
editorial content.

---

## 6. sidebar contract

The sidebar is shared across all pages within a package. Its content
is the same on every page; only the active state changes.

### 6.1 structure

```
kd-panels__sidebar
  kd-sidebar__section
    kd-sidebar__heading    "modules" (or "standard library" for core)
    kd-sidebar__link       one per module (active if current)
      kd-sidebar__fn       module name
    kd-sidebar__link--indent  one per pub fn in active module
      kd-sidebar__fn       .fn_name
      kd-badge             effect badge (IO, Fail, ->, etc.)

  kd-sidebar__rule

  kd-sidebar__section
    kd-sidebar__heading    "effects"
    kd-sidebar__link       one per pub effect
      kd-sidebar__fn       effect name
      kd-badge             "effect" tag

  kd-sidebar__rule

  kd-sidebar__section
    kd-sidebar__heading    "traits"
    kd-sidebar__link       one per pub trait
      kd-sidebar__fn       trait name
      kd-badge             "trait" tag
```

### 6.2 badge assignment

| item kind | badge class | text |
|---|---|---|
| pure function (`->`) | `kd-badge--pure` | `->` |
| IO function | `kd-badge--io` | `IO` |
| failing function (`Fail E`) | `kd-badge--fail` | `Fail` |
| async/send function | `kd-badge--async` | `Send` |
| effect declaration | inline style (scarlet-tinted) | `effect` |
| trait declaration | inline style (olive-tinted) | `trait` |

When a function has multiple effects, show the "most significant"
badge. Priority: IO > Fail > Send > other. Pure (`->`) only when
the effect set is empty.

---

## 7. migration note

The first implementation of `kea docs` will be in Rust, as part of
the bootstrap toolchain. It will be a standalone binary that:

1. Parses `.kea` source files (reusing the compiler's parser)
2. Extracts declarations, doc blocks, and signatures
3. Renders HTML using string templates
4. Copies static assets
5. Writes the output directory

The HTML output is the stable contract. The CSS class names (`kd-*`),
the page structure, the section ordering, the asset paths — these are
the API. The renderer internals are not.

When kea is self-hosting (Phase 3+), the generator can be rewritten
in kea itself, using the typed grammar (`Html` blocks from the
packaging brief). The output schema does not change. Pages still
reference `keadocs.css`. The same sidebar structure. The same
signature blocks. The same effect badges.

This means:
- The CSS bundle is stable and versioned independently
- The HTML structure is a contract, not an implementation detail
- Tests can snapshot HTML output and diff across generator versions
- The Rust implementation and the eventual kea implementation must
  produce byte-identical output for the same input (modulo whitespace)

The generator is a function: `Source × Manifest → HTML + Assets`.
Swap the internals, keep the contract.
