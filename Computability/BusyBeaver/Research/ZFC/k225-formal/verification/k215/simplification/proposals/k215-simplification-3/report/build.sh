#!/bin/sh
set -eu
cd "$(dirname "$0")"
# A conventional TeX Live installation needs no overrides. These optional
# settings also support installations with separate format and font trees.
export TEXMFVAR="${TEXMFVAR:-/tmp/k215-composed-selector-tex/var}"
export TEXMFCONFIG="${TEXMFCONFIG:-/tmp/k215-composed-selector-tex/config}"
if [ -n "${K215_TEXFORMATS:-}" ]; then
  export TEXFORMATS="$K215_TEXFORMATS:"
fi
if [ -d /usr/share/texmf ]; then
  export TEXINPUTS=".:/usr/share/texmf/tex//:/usr/share/texlive/texmf-dist/tex//:${TEXINPUTS:-}"
  export TEXFONTMAPS="/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//:${TEXFONTMAPS:-}"
  export TFMFONTS="/usr/share/texmf/fonts/tfm//:/usr/share/texlive/texmf-dist/fonts/tfm//:${TFMFONTS:-}"
  export T1FONTS="/usr/share/texmf/fonts/type1//:/usr/share/texlive/texmf-dist/fonts/type1//:${T1FONTS:-}"
  export ENCFONTS="/usr/share/texmf/fonts/enc//:/usr/share/texlive/texmf-dist/fonts/enc//:${ENCFONTS:-}"
fi
# A minimal Debian TeX tree can omit the generated default map. Supply only
# the standard map fragments used here; do not alter any system installation.
if ! kpsewhich pdftex.map >/dev/null 2>&1 && [ -f /usr/share/texmf/fonts/map/dvips/lm/lm.map ]; then
  mapdir="${TMPDIR:-/tmp}/k215-composed-selector-tex/maps"
  mkdir -p "$mapdir"
  cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map > "$mapdir/pdftex.map"
  export TEXFONTMAPS="$mapdir:${TEXFONTMAPS:-}"
fi
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
