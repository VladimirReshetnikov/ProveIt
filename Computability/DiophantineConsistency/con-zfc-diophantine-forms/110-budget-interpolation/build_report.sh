#!/bin/sh
set -eu
cd "$(dirname "$0")/report"
# Standard installations need no special configuration. A prepared research
# container may already contain this local format and font-map fallback.
if [ -z "$(kpsewhich -format=fmt pdflatex.fmt 2>/dev/null || true)" ] && [ -f /tmp/wave13_tex/pdflatex.fmt ]; then
 export TEXFORMATS=/tmp/wave13_tex:
 export TEXINPUTS=.:/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:
 export TFMFONTS=/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//:
 export TEXFONTMAPS=/tmp/wave13_tex:/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//:
 export T1FONTS=/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//:
 export ENCFONTS=/usr/share/texlive/texmf-dist/fonts/enc//:/usr/share/texmf/fonts/enc//:
 export VFFONTS=/usr/share/texlive/texmf-dist/fonts/vf//:/usr/share/texmf/fonts/vf//:
fi
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
