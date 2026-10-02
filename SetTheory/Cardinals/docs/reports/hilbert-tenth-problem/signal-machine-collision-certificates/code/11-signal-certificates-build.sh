#!/bin/sh
# Build the editable LaTeX article; all generated files stay under ./build.
set -eu
cd "$(dirname "$0")"
ROOT=$(pwd)
BUILD="$ROOT/build"
mkdir -p "$BUILD"
export SOURCE_DATE_EPOCH=1790899200
export FORCE_SOURCE_DATE=1
# Some minimal containers ship TeX files without an ls-R database.
if ! kpsewhich article.cls >/dev/null 2>&1; then
  if [ -d /usr/share/texlive/texmf-dist ] && [ -d /usr/share/texmf ]; then
    TEXMF="{$BUILD/texmf,/usr/share/texlive/texmf-dist,/usr/share/texmf}"
    export TEXMF
  else
    echo 'A working TeX Live installation is required.' >&2
    exit 1
  fi
fi
FORMAT=$(kpsewhich pdflatex.fmt || true)
if [ -z "$FORMAT" ]; then
  FORMAT="$BUILD/pdflatex.fmt"
  if [ ! -f "$FORMAT" ]; then
    pdflatex -ini -interaction=nonstopmode -halt-on-error -jobname=pdflatex \
      -output-directory="$BUILD" -progname=pdflatex '*pdflatex.ini' >"$BUILD/format-build.log" 2>&1
  fi
fi
# Generate only the small local font map when a system map is absent.
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : > "$BUILD/pdftex.map"
  for name in lm.map cm.map symbols.map; do
    map=$(kpsewhich "$name")
    cat "$map" >> "$BUILD/pdftex.map"
  done
  TEXFONTMAPS="$BUILD:"
  export TEXFONTMAPS
fi
for pass in 1 2 3; do
  pdflatex -fmt="$FORMAT" -interaction=nonstopmode -halt-on-error \
    -output-directory="$BUILD" article.tex >"$BUILD/pass-$pass.log" 2>&1 || {
      cat "$BUILD/pass-$pass.log" >&2; exit 1;
    }
done
cp "$BUILD/article.pdf" "$ROOT/article.pdf"
printf 'Built %s\n' "$ROOT/article.pdf"
