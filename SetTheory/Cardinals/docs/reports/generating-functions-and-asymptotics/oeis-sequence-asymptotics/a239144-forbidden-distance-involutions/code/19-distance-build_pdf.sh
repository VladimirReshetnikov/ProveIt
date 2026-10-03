#!/usr/bin/env bash
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
BUILD=${BUILD_DIR:-"$ROOT/pdf-build"}
mkdir -p "$BUILD"
BUILD=$(CDPATH= cd -- "$BUILD" && pwd)
export TEXMFVAR="$BUILD/texmf-var" TEXMFCONFIG="$BUILD/texmf-config" TEXMFCACHE="$BUILD/texmf-cache"
mkdir -p "$TEXMFVAR" "$TEXMFCONFIG" "$TEXMFCACHE"
# Requires a local TeX distribution; never downloads or installs software.
# Some container distributions have dangling TeX filename databases. This
# optional fallback lets kpathsea search their actual installed directories.
if ! kpsewhich latex.ltx >/dev/null 2>&1; then
  if [ -d /usr/share/texmf ] && [ -d /usr/share/texlive/texmf-dist ]; then
    export TEXMF='{/usr/share/texmf,/usr/share/texlive/texmf-dist}'
  fi
fi
cd "$BUILD"
FORMAT_ARGS=()
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  pdftex -ini -etex -jobname=pdflatex -interaction=nonstopmode '\input pdflatex.ini' > format-build.log
  FORMAT_ARGS=(-fmt="$BUILD/pdflatex.fmt")
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : > pdftex.map
  for MAP in lm.map cm.map cmextra.map symbols.map; do
    SOURCE=$(kpsewhich "$MAP")
    cat "$SOURCE" >> pdftex.map
  done
fi
pdflatex "${FORMAT_ARGS[@]}" -interaction=nonstopmode -halt-on-error "$ROOT/article.tex"
pdflatex "${FORMAT_ARGS[@]}" -interaction=nonstopmode -halt-on-error "$ROOT/article.tex"
printf '\nBuilt %s\n' "$BUILD/article.pdf"
