#!/bin/sh
# Rebuild the article with TeX Live. Generated files remain in .build.
set -eu
cd "$(dirname "$0")"
ROOT=$(pwd)
mkdir -p .build
if ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
export TEXMFVAR="$ROOT/.build" TEXMFCONFIG="$ROOT/.build" TEXFORMATS="$ROOT/.build:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd .build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini > format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : > .build/pdftex.map
  for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
    cat "$(kpsewhich "$name")" >> .build/pdftex.map
  done
  export TEXFONTMAPS="$ROOT/.build:"
fi
export SOURCE_DATE_EPOCH=1790899200 FORCE_SOURCE_DATE=1
cd paper
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$ROOT/.build" waterfall-diophantine.tex > "$ROOT/.build/compile-$pass.log" 2>&1 || { tail -80 "$ROOT/.build/compile-$pass.log"; exit 1; }
done
cp "$ROOT/.build/waterfall-diophantine.pdf" "$ROOT/waterfall-diophantine.pdf"
echo "Built waterfall-diophantine.pdf"
