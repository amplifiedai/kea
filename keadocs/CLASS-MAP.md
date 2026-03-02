# keadocs class name contract

The canonical CSS class names are defined in `keadocs/css/keadocs.css`.
All generator output MUST use `kd-*` prefixed classes.

The reference mock (`kea-reference-v2.html`) used unprefixed class names
during exploratory design. This document maps mock → canonical for anyone
reading both.

## Layout

| mock class | canonical class | notes |
|---|---|---|
| `layout` | `kd-panels` | three-panel grid |
| `sidebar` | `kd-panels__sidebar` | left panel |
| `content` | `kd-panels__main` | center panel |

## Navigation

| mock | canonical |
|---|---|
| `topnav` | `kd-nav` |
| `topnav-logo` | `kd-nav__logo` |
| `topnav-sep` | `kd-nav__sep` |
| `topnav-tab` | `kd-nav__link` |
| `topnav-tab active` | `kd-nav__link kd-nav__link--active` |
| `topnav-spacer` | `kd-nav__spacer` |
| `topnav-search` | `kd-nav__search` |
| `topnav-ext` | `kd-nav__ext` |

## Sidebar

| mock | canonical |
|---|---|
| `sb-label` | `kd-sidebar__heading` |
| `sb-item` | `kd-sidebar__link` |
| `sb-item active` | `kd-sidebar__link kd-sidebar__link--active` |
| `sb-item sb-indent` | `kd-sidebar__link kd-sidebar__link--indent` |
| `sb-fn` | `kd-sidebar__fn` |
| `sb-badge` | `kd-badge` |
| `sb-badge badge-io` | `kd-badge kd-badge--io` |
| `sb-rule` | `kd-sidebar__rule` |

## Page header

| mock | canonical |
|---|---|
| `page-hd` | `kd-page-header` |
| `page-title` | `kd-page-title` |
| `page-meta` | `kd-page-meta` |
| `tag tag-effect` | `kd-page-tag kd-page-tag--effect` |
| `tag tag-struct` | `kd-page-tag kd-page-tag--struct` |
| `tag tag-enum` | `kd-page-tag kd-page-tag--enum` |
| `page-desc` | `kd-page-desc` |
| `src-link` | `kd-src-link` |
| `bc` | `kd-breadcrumb` |
| `bc-sep` | `kd-breadcrumb__sep` |

## Signatures

| mock | canonical |
|---|---|
| `sig` | `kd-sig` |
| `sig effectful` | `kd-sig kd-sig--effectful` |
| `sig polymorphic` | `kd-sig kd-sig--polymorphic` |
| `effect-decl` | `kd-effect-decl` |

## Effect expand panel

| mock | canonical |
|---|---|
| `ef-expand` | `kd-expand` |
| (visible state) | `kd-expand kd-expand--visible` |
| `ef-row` | `kd-expand__row` |
| `ef-label` | `kd-expand__label` |
| `ef-desc` | `kd-expand__desc` |
| `ef-hover` | `kd-effect-trigger` |

## Function entries

| mock | canonical |
|---|---|
| `fn-entry` | `kd-fn-entry` |
| `fn-name` | `kd-fn-name` |
| `fn-doc` | `kd-fn-doc` |
| `ex-label` | `kd-example-label` |
| `ex` | `kd-example` |

## Handler panel

| mock | canonical |
|---|---|
| `handler-panel` | `kd-handler-panel` |
| `handler-panel-title` | `kd-handler-panel__title` |
| `handler-row` | `kd-handler-panel__row` |
| `handler-name` | `kd-handler-panel__name` |
| `handler-desc` | `kd-handler-panel__desc` |

## Syntax highlighting

| mock | canonical |
|---|---|
| `kw` | `kd-syn-keyword` |
| `ty` | `kd-syn-type` |
| `ef` | `kd-syn-effect` |
| `str` | `kd-syn-string` |
| `cmt` | `kd-syn-comment` |
| `fn-n` | `kd-syn-function` |
| `op` | `kd-syn-operator` |
| `param` | `kd-syn-param` |

## Other components

| mock | canonical |
|---|---|
| `section-label` | `kd-section-label` |
| `section-rule` | `kd-rule--section` (on `<hr>`) |
| `footer` | `kd-footer` |
| `footer-logo` | `kd-footer__logo` |
| `footer-links` | `kd-footer__links` |
| `footer-spacer` | `kd-footer__spacer` |
| `footer-ver` | `kd-footer__version` |

## Effect arrow

| mock | canonical |
|---|---|
| `ef` (on arrow brackets) | `kd-arrow` |
| (pure arrow) | `kd-arrow--pure` |

## Badges

| mock | canonical |
|---|---|
| `sb-badge badge-io` | `kd-badge kd-badge--io` |
| `sb-badge badge-fail` | `kd-badge kd-badge--fail` |
| `sb-badge badge-async` | `kd-badge kd-badge--async` |
| `sb-badge` (pure) | `kd-badge kd-badge--pure` |

## Type links

| mock | canonical |
|---|---|
| `ty` (as `<a>`) | `kd-type-link` |
