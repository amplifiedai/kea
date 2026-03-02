# keadocs fonts

This directory holds the woff2 font files shipped with `kea doc` output.
All fonts are OFL-licensed (SIL Open Font License).

## Setup

Run the download script once after cloning:

```sh
chmod +x keadocs/fonts/download.sh
keadocs/fonts/download.sh
```

The `.woff2` files are `.gitignored`. CI should run this script before
building docs.

## Required files

### Syne (display / headings)
- `Syne-VariableFont_wght.woff2`

### Literata (body text)
- `Literata-VariableFont_opsz,wght.woff2`
- `Literata-Italic-VariableFont_opsz,wght.woff2`

### IBM Plex Mono (code)
- `IBMPlexMono-Light.woff2` (300)
- `IBMPlexMono-Regular.woff2` (400)
- `IBMPlexMono-Italic.woff2` (400 italic)
- `IBMPlexMono-Medium.woff2` (500)
- `IBMPlexMono-SemiBold.woff2` (600)
- `IBMPlexMono-Bold.woff2` (700)

## Sources

- Syne: https://fonts.google.com/specimen/Syne
- Literata: https://fonts.google.com/specimen/Literata
- IBM Plex Mono: https://fonts.google.com/specimen/IBM+Plex+Mono
