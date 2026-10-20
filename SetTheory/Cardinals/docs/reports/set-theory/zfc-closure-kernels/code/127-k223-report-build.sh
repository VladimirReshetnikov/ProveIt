#!/bin/sh
set -eu
cd "$(dirname "$0")"
# A normal TeX Live installation needs no overrides. The fallbacks below also
# support the supplied research container's separate format and font trees.
export TEXMFVAR="${TEXMFVAR:-/tmp/k223-tex/var}"
export TEXMFCONFIG="${TEXMFCONFIG:-/tmp/k223-tex/config}"
export TEXINPUTS=".:/usr/share/texmf/tex//:/usr/share/texlive/texmf-dist/tex//:${TEXINPUTS:-}"
if [ -n "${K223_TEXFORMATS:-}" ]; then
  export TEXFORMATS="$K223_TEXFORMATS:"
elif [ -f ../../research_sub246/deliverable/report/pdflatex.fmt ]; then
  export TEXFORMATS="$(cd ../../research_sub246/deliverable/report && pwd):"
fi
export TEXFONTMAPS="/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//:${TEXFONTMAPS:-}"
export TFMFONTS="/usr/share/texmf/fonts/tfm//:/usr/share/texlive/texmf-dist/fonts/tfm//:${TFMFONTS:-}"
export T1FONTS="/usr/share/texmf/fonts/type1//:/usr/share/texlive/texmf-dist/fonts/type1//:${T1FONTS:-}"
export ENCFONTS="/usr/share/texmf/fonts/enc//:/usr/share/texlive/texmf-dist/fonts/enc//:${ENCFONTS:-}"
pdflatex -interaction=nonstopmode -halt-on-error report.tex > build.log
pdflatex -interaction=nonstopmode -halt-on-error report.tex >> build.log
