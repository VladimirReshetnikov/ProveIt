#!/usr/bin/env bash
# Rebuild with writable package-local caches; never modify system TeX files.
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$PWD"
BUILD="$ROOT/.build"
mkdir -p "$BUILD"
command -v kpsewhich >/dev/null
command -v pdftex >/dev/null
command -v pdflatex >/dev/null
# Minimal containers can have installed TeX files but absent ls-R databases.
# Removing the database-only search restriction lets kpathsea find those files.
if [[ -z "${TEXMF:-}" ]] && [[ -d /usr/share/texlive/texmf-dist ]] && ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
fi
export TEXMFVAR="$BUILD"
export TEXMFCONFIG="$BUILD"
export TEXFORMATS="$BUILD:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd "$BUILD" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error \
    -jobname=pdflatex -progname=pdflatex pdflatex.ini > format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : > "$BUILD/pdftex.map"
  for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
    map=$(kpsewhich "$name") || { echo "Missing installed font map: $name" >&2; exit 1; }
    cat "$map" >> "$BUILD/pdftex.map"
  done
  export TEXFONTMAPS="$BUILD:"
fi
# Reproducible PDF timestamps; the article date is set explicitly in its source.
export SOURCE_DATE_EPOCH=1790899200
export FORCE_SOURCE_DATE=1
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" \
    "$ROOT/article/regular-cyclic-word-covers.tex" > "$BUILD/compile-$pass.log"
done
cp "$BUILD/regular-cyclic-word-covers.pdf" "$ROOT/article/regular-cyclic-word-covers.pdf"
printf 'Built %s\n' "$ROOT/article/regular-cyclic-word-covers.pdf"
