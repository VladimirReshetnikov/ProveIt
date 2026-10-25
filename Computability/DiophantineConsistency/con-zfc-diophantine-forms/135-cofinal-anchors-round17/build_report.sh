#!/bin/sh
# Build the editable TeX report without touching system TeX configuration.
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$HERE/report"
# Explicit trees avoid distributions with absent filename databases.
if [ -d /usr/share/texlive/texmf-dist ] && [ -d /usr/share/texmf ]; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  mkdir -p .tex
  (cd .tex && pdftex -etex -ini -jobname=pdflatex -progname=pdflatex '\input pdflatex.ini')
  FMT='-fmt=.tex/pdflatex.fmt'
else
  FMT=''
fi
for pass in 1 2 3; do
  pdflatex $FMT -interaction=nonstopmode -halt-on-error main.tex
done
cp main.pdf "$HERE/ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.pdf"
