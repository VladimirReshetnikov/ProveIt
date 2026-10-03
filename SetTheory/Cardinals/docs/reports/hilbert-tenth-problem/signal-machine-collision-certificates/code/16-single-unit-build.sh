#!/bin/sh
# Portable TeX Live rebuild; all caches stay in this package.
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
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$ROOT/.build" single-unit-mass-three.tex >"$ROOT/.build/compile-$pass.log" 2>&1 || { tail -80 "$ROOT/.build/compile-$pass.log"; exit 1; }
done
cp .build/single-unit-mass-three.pdf single-unit-mass-three.pdf
printf '%s\n' 'Built single-unit-mass-three.pdf'
