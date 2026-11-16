#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p .build/pdf
if ! kpsewhich pdflatex.ini >/dev/null 2>&1 && [ -d /usr/share/texlive/texmf-dist ]; then
  export TEXMF='{/usr/share/texmf,/usr/share/texlive/texmf-dist}'
fi
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  mkdir -p .build/format
  if [ ! -f .build/format/pdflatex.fmt ]; then
    (cd .build/format && pdftex -ini -etex -interaction=nonstopmode \
      -jobname=pdflatex -progname=pdflatex '\input pdflatex.ini')
  fi
  export TEXFORMATS="$PWD/.build/format:"
  export TEXFONTMAPS="$PWD/.build/format//:"
  if [ ! -f .build/format/pdftex.map ]; then
    cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cmextra.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/latxfont.map \
      > .build/format/pdftex.map
  fi
fi
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=.build/pdf paper.tex
cp .build/pdf/paper.pdf ipra_presentations_to_witnesses.pdf
