# Kea Design System

*Source of truth for visual identity across kea.dev, keadocs, and all official materials.*

## Thesis

Kea is a language where one mechanism does many things. Row polymorphism unifies records and effects. The struct is the universal unit. The handler is the universal seam. Small set of primitives, emergent power from composition.

Bauhaus is the same idea applied to visual form. Elementary shapes. Primary relationships. Functional composition. The design system embodies: **compositional minimalism that reveals unexpected depth**.

The kea bird is the metaphor made physical: olive-green camouflage (surface simplicity), scarlet-orange underwings (hidden power), visible only in flight (only when the thing is working).

---

## Logo

The logo is the effect arrow itself.

```
-[kea]>
```

It's valid Kea syntax (an effect signature). Pure typography — no icon. The brackets contain the name the way effects contain capabilities. The arrow points forward.

**Rendering:** monospace, single weight, one size. Set in IBM Plex Mono at display sizes. At small sizes (nav bars, footers), the brackets and arrow are structural characters, not decoration.

**Variants:**
- `-[kea]>` — full mark
- `->` — pure arrow (favicon, small mark)
- `-[ ]>` — empty effect set (secondary mark)

**Color in logo:** the brackets and arrow may be rendered in scarlet (`-[`kea`]>`) to echo the effect arrow's role. The name stays in the heading color. This is optional — monochrome is the default.

**No representational bird imagery.** The PEDAGOGY.md commits to not using Māori visual culture. The effect arrow is the identity.

---

## Color Palette

Derived from the kea's plumage. Mapped to Bauhaus-Kandinsky color relationships: warm/cool polarity, advancing (scarlet, gold) vs receding (teal, olive).

### Primary

| Name | Hex | Role | Source |
|------|-----|------|--------|
| olive | `#4A5A2B` | Ground, structure, purity | Dominant body plumage |
| scarlet | `#C8432B` | Accent, reveal, effects | Underwing flash |
| teal | `#2B6B6B` | Links, types, architecture | Rump and tail |
| gold | `#C4982B` | Warmth, annotation, warning | Inner feathers |

### Structural

| Name | Hex | Role |
|------|-----|------|
| ink | `#1C1A18` | Headings, display text |
| slate | `#3A3632` | Body text |
| slate-light | `#7A7268` | Secondary text |
| stone | `#E8E2D8` | Borders, rules, surfaces |
| bone | `#F4F0E8` | Code backgrounds, cards |
| paper | `#FAF8F4` | Page background |

### Semantic usage

- **Scarlet is rare.** Like the underwing, it appears at moments of revelation: the first effect arrow, hover states, active elements, the `-[...]>` syntax. Never decorative.
- **Olive is structural.** Rules, borders, active sidebar items, pure-function indicators. The ground everything sits on.
- **Teal is navigational.** Links, type names in code, cross-references. Hover state transitions to scarlet (cool → warm, the "reveal").
- **Gold is cautionary.** Warnings, `Fail` badges, deprecation notices. Warm but not alarming.

### Effect arrow coloring

The effect arrow `-[IO, Fail E]>` has specific coloring rules:
- The brackets and arrow (`-[` `]>`) are always scarlet
- Effect names inside use their badge colors (IO → olive, Fail → gold, Async → teal)
- The pure arrow `->` is olive or neutral, never scarlet

### Signature block borders

Function signature blocks have a left border indicating purity:
- `olive` — pure functions (`->`)
- `scarlet` — effectful functions (`-[...]>`)
- `teal` — effect-polymorphic functions (`-[e]>`)

---

## Dark Mode

**Philosophy:** invert the ground, not the logic. Color relationships stay identical. The palette shifts as if the kea moved from daylight to dusk.

### Mapping

```
                       light              dark
────────────────────────────────────────────────────
background             paper #FAF8F4      #151311
surface                bone  #F4F0E8      #1E1C19
elevated               stone #E8E2D8      #252220

body text              slate #3A3632      #D0C8BE
heading text           ink   #1C1A18      #FAF8F4
secondary text         slate-light        #8A8070

code background        bone  #F4F0E8      #1A1816
code border (olive)    #4A5A2B            #6B8240
code border (scarlet)  #C8432B            #E05A3F
code border (teal)     #2B6B6B            #3FA0A0

link                   teal  #2B6B6B      #4AADAD
link hover             scarlet #C8432B    #E86040

effect arrow           scarlet            #E86040
```

### Implementation

- CSS custom properties with `--kd-` prefix
- Respect `prefers-color-scheme` by default
- Manual toggle via `data-theme="dark"` on `<html>`, stored in `localStorage`
- Toggle indicator: `○ / ●` (abstract, not representational)

---

## Typography

### Typeface selection

| Role | Family | Rationale |
|------|--------|-----------|
| Display / headings | **Syne** | Geometric, idiosyncratic. The 'g' and 'a' are distinctive. Feels like a language that's "familiar but different." |
| Body text | **Literata** | Variable serif for screen reading. Scholarly without stuffy. Optical sizes sharpen at small sizes. |
| Code | **IBM Plex Mono** | Geometric Bauhaus-lineage clarity. Deeply legible. Variable font. |

### Conventions

- **All lowercase headings.** Following the Bauhaus tradition (Bayer: why two alphabets?). The only capitals appear in code (type names: `String`, `Int`, `User`).
- **Variable fonts only.** Three requests total: Syne, Literata, IBM Plex Mono. `font-display: swap`.
- **rem-based sizing.** Respects user font preferences.

### Type scale

Two density modes:

```
                    reading (book/landing)   reference (API docs)
────────────────────────────────────────────────────────────────
base                1.06rem / 1.72           0.95rem / 1.6
code inline         0.87em                   0.85em
code block          0.86rem / 1.7            0.82rem / 1.6
h1 (page title)     2.25rem                  1.7rem
h2 (section)        1.7rem                   1.28rem
h3 (subsection)     1.28rem                  1.06rem
signature block     0.9rem / 1.55            0.86rem / 1.5
sidebar             0.78rem                  0.75rem
badge               0.65rem                  0.65rem
```

---

## Syntax Highlighting

Same semantic mapping in both light and dark modes.

```
                       light              dark
────────────────────────────────────────────────────
keyword (fn, let, match, if)
                       teal #2B6B6B       #5EC4C4
type name (String, Int, List)
                       olive #4A5A2B      #8AAD50
effect annotation (-[IO]>)
                       scarlet #C8432B    #E86040
string literal
                       gold-muted #A68834 #D4B85C
comment (--)
                       slate-light #7A7268 #8A8070
function name
                       ink #1C1A18        #FAF8F4
operator (=, +, ->)
                       slate-light        #8A8070
parameter name
                       slate (light weight) same
```

Keywords are cool. Types are grounded. Effects are hot. Strings are warm. Comments recede.

---

## Effect Badges

Compact indicators used in sidebars, search results, and tooltips:

```
[IO]      olive background, ink text
[Fail E]  gold background, ink text
[Async]   teal background, bone text
[->]      stone background, slate text (pure)
```

Monospace, xs font, rectangular (no border-radius).

---

## Layout Principles

### The manuscript layout

Single wide column, left-aligned, generous left margin. Right margin is alive with annotations, cross-references, effect signatures. Like a technical manuscript or academic paper.

### Horizontal rules as architecture

- Thick olive rule: major section boundaries
- Medium ink rule: subsection boundaries
- Thin stone rule: item separators
- Scarlet rule: appears exactly once on the landing page, above the first effect arrow reveal

### Navigation

Persistent nav bar, slim, monospace, bottom-bordered. Active section gets olive underline.

kealang.org:
```
-[kea]>  │  docs  reference  spec  errors  source
```

packages.kealang.org:
```
pkg_name 0.1.0  │  guides  reference  [source]     [search ⌘K]  [○/●]  [kealang.org ↗]
```

---

## CSS Custom Property Namespace

All keadocs variables use `--kd-` prefix:

```css
--kd-olive, --kd-scarlet, --kd-teal, --kd-gold
--kd-ink, --kd-slate, --kd-stone, --kd-bone, --kd-paper
--kd-bg, --kd-text, --kd-heading, --kd-link, --kd-effect
--kd-code-bg, --kd-sig-bg, --kd-border
--kd-font-display, --kd-font-body, --kd-font-mono
```

---

## Products

| Product | Domain | Repo | Design mode |
|---------|--------|------|-------------|
| Landing page | kealang.org | kea-www | reading (manuscript) |
| The book | kealang.org/docs | kea-www | reading (manuscript) |
| Kernel spec | kealang.org/spec | kea-www | reading (manuscript, heavy margin) |
| Error catalog | kealang.org/errors | kea-www | unique (card per error) |
| Package registry | packages.kealang.org | kea-packages | reference (three-panel) |
| Stdlib docs | packages.kealang.org/core | kea-packages | reference (three-panel) |
| Community docs | packages.kealang.org/{pkg} | kea-packages | reference + guides |

All share this design system. The keadocs asset bundle (CSS, fonts, JS) ships with the `kea` tool and is the source of truth.
