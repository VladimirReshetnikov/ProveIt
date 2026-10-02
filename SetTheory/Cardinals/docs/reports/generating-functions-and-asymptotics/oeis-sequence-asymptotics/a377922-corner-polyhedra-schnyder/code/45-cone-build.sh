#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
export SOURCE_DATE_EPOCH=1790899200
export FORCE_SOURCE_DATE=1
# Fallback for a TeX Live tree whose filename database is not installed.
if [[ -z "${TEXMF:-}" ]] && [[ -d /usr/share/texlive/texmf-dist ]] && ! kpsewhich article.cls >/dev/null 2>&1; then
 export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
fi
export TEXMFVAR="$PWD/build"
export TEXMFCONFIG="$PWD/build"
export TEXFORMATS="$PWD/build:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
 (cd build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini > format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
 : > build/pdftex.map
 for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
  map_path="$(kpsewhich "$name")"
  [[ -z "$map_path" ]] || cat "$map_path" >> build/pdftex.map
 done
 export TEXFONTMAPS="$PWD/build:"
fi
for pass in 1 2; do
 pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > "build/compile-$pass.txt"
done
cp build/article.pdf article.pdf
printf 'Built article.pdf\n'
