#!/usr/bin/env bash
set -euo pipefail

# Download fonts for keadocs.
# Run once after cloning the repo. Fonts are .gitignored.
#
# All fonts are OFL-licensed (SIL Open Font License).

FONT_DIR="$(cd "$(dirname "$0")" && pwd)"
echo "Downloading fonts to $FONT_DIR ..."

extract_first_woff2_url() {
  local css_url="$1"
  curl -fsSL "$css_url" -H "User-Agent: Mozilla/5.0" \
    | tr -d '\r' \
    | sed -nE "s/.*url\\(([^)]+\\.woff2)\\).*/\\1/p" \
    | head -1
}

# --- Syne (variable, wght 400–800) ---
echo "  Syne..."
curl -fsSL -o "$FONT_DIR/Syne-VariableFont_wght.woff2" \
  "https://github.com/nicholasdavies/syne-font/raw/main/fonts/variable/Syne-VariableFont_wght.woff2" \
  2>/dev/null || {
    # Fallback: Google Fonts API
    echo "    (trying Google Fonts API fallback)"
    URL=$(extract_first_woff2_url "https://fonts.googleapis.com/css2?family=Syne:wght@400..800&display=swap")
    curl -fsSL -o "$FONT_DIR/Syne-VariableFont_wght.woff2" "$URL"
  }

# --- Literata (variable, opsz+wght) ---
echo "  Literata (regular)..."
URL=$(extract_first_woff2_url "https://fonts.googleapis.com/css2?family=Literata:opsz,wght@7..72,200..900&display=swap")
curl -fsSL -o "$FONT_DIR/Literata-VariableFont_opsz,wght.woff2" "$URL"

echo "  Literata (italic)..."
URL=$(extract_first_woff2_url "https://fonts.googleapis.com/css2?family=Literata:ital,opsz,wght@1,7..72,200..900&display=swap")
curl -fsSL -o "$FONT_DIR/Literata-Italic-VariableFont_opsz,wght.woff2" "$URL"

# --- IBM Plex Mono (individual weights) ---
PLEX_BASE="https://github.com/IBM/plex/raw/master/IBM-Plex-Mono/fonts/complete/woff2"

for WEIGHT in Light Regular Italic Medium SemiBold Bold; do
  echo "  IBM Plex Mono ($WEIGHT)..."
  curl -fsSL -o "$FONT_DIR/IBMPlexMono-${WEIGHT}.woff2" \
    "$PLEX_BASE/IBMPlexMono-${WEIGHT}.woff2" 2>/dev/null || {
      # Fallback: try the split directory structure
      curl -fsSL -o "$FONT_DIR/IBMPlexMono-${WEIGHT}.woff2" \
        "https://github.com/IBM/plex/raw/master/packages/plex-mono/fonts/complete/woff2/IBMPlexMono-${WEIGHT}.woff2"
    }
done

echo ""
echo "Done. Font files in $FONT_DIR:"
ls -la "$FONT_DIR"/*.woff2 2>/dev/null || echo "  (no woff2 files found — check errors above)"
