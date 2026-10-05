#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
export TZ=UTC
export SOURCE_DATE_EPOCH=1790899200
export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
export TEXMFVAR="$PWD/build/texmf-var"
export TEXMFCONFIG="$PWD/build/texmf-config"
export TEXFORMATS="$PWD/build//:"
if [ ! -f build/pdflatex.fmt ]; then
 (cd build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex pdflatex.ini > format.stdout)
fi
for pass in 1 2; do
 pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build '\pdfinfoomitdate=1\pdftrailerid{}\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{article.tex}' > "build/pass-$pass.stdout"
done
cp build/article.pdf article.pdf
