#!/bin/sh
# Rebuild the report with TeX Live. Generated files stay in .build/.
set -eu
cd "$(dirname "$0")"
ROOT=$(pwd)
mkdir -p .build
if ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
export TEXMFVAR="$ROOT/.build" TEXMFCONFIG="$ROOT/.build" TEXFORMATS="$ROOT/.build:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd .build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini >format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : >.build/pdftex.map
  for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
    cat "$(kpsewhich "$name")" >>.build/pdftex.map
  done
  export TEXFONTMAPS="$ROOT/.build:"
fi
export TZ=UTC SOURCE_DATE_EPOCH=1790985600 FORCE_SOURCE_DATE=1
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$ROOT/.build" report17.tex >"$ROOT/.build/compile-$pass.log" 2>&1 || { tail -80 "$ROOT/.build/compile-$pass.log"; exit 1; }
done
cp .build/report17.pdf report17.pdf
printf '%s\n' 'Built report17.pdf'
