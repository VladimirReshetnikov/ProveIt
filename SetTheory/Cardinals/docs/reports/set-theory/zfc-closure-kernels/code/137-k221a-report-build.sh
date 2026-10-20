#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export TEXMFVAR="${TEXMFVAR:-/tmp/sub221-tex/var}"
export TEXMFCONFIG="${TEXMFCONFIG:-/tmp/sub221-tex/config}"
export TEXINPUTS=".:/usr/share/texmf/tex//:/usr/share/texlive/texmf-dist/tex//:${TEXINPUTS:-}"
if [ -n "${SUB221_TEXFORMATS:-}" ]; then
  export TEXFORMATS="$SUB221_TEXFORMATS:"
elif [ -f ../../research_sub246/deliverable/report/pdflatex.fmt ]; then
  export TEXFORMATS="$(cd ../../research_sub246/deliverable/report && pwd):"
fi
export TEXFONTMAPS="/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//:${TEXFONTMAPS:-}"
export TFMFONTS="/usr/share/texmf/fonts/tfm//:/usr/share/texlive/texmf-dist/fonts/tfm//:${TFMFONTS:-}"
export T1FONTS="/usr/share/texmf/fonts/type1//:/usr/share/texlive/texmf-dist/fonts/type1//:${T1FONTS:-}"
export ENCFONTS="/usr/share/texmf/fonts/enc//:/usr/share/texlive/texmf-dist/fonts/enc//:${ENCFONTS:-}"
pdflatex -interaction=nonstopmode -halt-on-error report.tex > build-pass1.log
pdflatex -interaction=nonstopmode -halt-on-error report.tex > build-pass2.log
mkdir -p render
rm -f render/page-*.png
pdftoppm -r 110 -png report.pdf render/page >/dev/null 2>&1
pdfinfo report.pdf > pdfinfo.txt
pdftotext -layout report.pdf report.txt
