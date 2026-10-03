#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd -- "$(dirname -- "$0")" && pwd)
BUILD=${BUILD_DIR:-$(mktemp -d)}
mkdir -p "$BUILD"
# Prefer the installed TeX defaults; explicit recursive paths also support minimal
# TeX Live containers whose filename database or user format cache is absent.
export TEXINPUTS="$ROOT/article:/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:${TEXINPUTS:-}"
export TFMFONTS="/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//:${TFMFONTS:-}"
export VFFONTS="/usr/share/texlive/texmf-dist/fonts/vf//:/usr/share/texmf/fonts/vf//:${VFFONTS:-}"
export T1FONTS="/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//:${T1FONTS:-}"
export ENCFONTS="/usr/share/texlive/texmf-dist/fonts/enc//:/usr/share/texmf/fonts/enc//:${ENCFONTS:-}"
export TEXFONTMAPS="$BUILD:/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//:${TEXFONTMAPS:-}"
export TEXMFVAR="$BUILD/texmf-var" TEXMFCONFIG="$BUILD/texmf-config"
# Build a local font map only on installations lacking a generated map.
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/*.map >"$BUILD/pdftex.map"
fi
export SOURCE_DATE_EPOCH=1790985600 FORCE_SOURCE_DATE=1
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd "$BUILD" && pdftex -ini -interaction=nonstopmode -jobname=pdflatex -progname=pdflatex -etex '\input latex.ltx' >format.log)
  export TEXFORMATS="$BUILD:${TEXFORMATS:-}"
fi
for pass in 1 2; do
  pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" "$ROOT/article/membrane_frontend.tex" >"$BUILD/pass-$pass.log"
done
cp "$BUILD/membrane_frontend.pdf" "$ROOT/article/membrane_frontend.pdf"
printf 'PDF built successfully\n'
