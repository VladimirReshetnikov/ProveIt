#!/usr/bin/env bash
# Rebuild with an installed TeX Live. No downloads or package installation.
# If its format cache is absent, initialize a local format from installed files.
set -euo pipefail
cd "$(dirname "$0")"
dist="$(kpsewhich --var-value=TEXMFDIST)"
if [[ -d "$dist/tex" ]]; then
  export TEXINPUTS="$dist/tex//:${TEXINPUTS:-}"
  export TFMFONTS="$dist/fonts/tfm//:${TFMFONTS:-}"
  export T1FONTS="$dist/fonts/type1//:${T1FONTS:-}"
  export TEXFONTMAPS="$dist/fonts/map//:${TEXFONTMAPS:-}"
fi
if ! kpsewhich -format=fmt pdflatex.fmt >/dev/null 2>&1; then
  mkdir -p .tex-runtime
  if [[ ! -f .tex-runtime/pdflatex.fmt ]]; then
    pdftex -ini -etex -interaction=nonstopmode -halt-on-error \
      -output-directory=.tex-runtime -jobname=pdflatex pdflatex.ini
  fi
  export TEXFORMATS="$PWD/.tex-runtime:${TEXFORMATS:-}"
fi
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
