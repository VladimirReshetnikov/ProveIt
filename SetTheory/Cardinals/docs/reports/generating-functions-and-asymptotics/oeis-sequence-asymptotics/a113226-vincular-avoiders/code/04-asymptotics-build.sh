#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p .build
if [[ -f /tmp/hamiltonian-rank-build/pdflatex.fmt ]]; then
  cp /tmp/hamiltonian-rank-build/pdflatex.fmt /tmp/hamiltonian-rank-build/pdftex.map .build/
  export TEXINPUTS=".:/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:"
  export TEXFORMATS="$PWD/.build:"
  export TEXFONTMAPS="$PWD/.build:/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//:"
  export TFMFONTS="/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//:"
  export VFFONTS="/usr/share/texlive/texmf-dist/fonts/vf//:/usr/share/texmf/fonts/vf//:"
  export T1FONTS="/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//:"
  export ENCFONTS="/usr/share/texlive/texmf-dist/fonts/enc//:/usr/share/texmf/fonts/enc//:"
fi
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build a113226-asymptotics.tex > .build/pass${pass}.log
done
cp .build/a113226-asymptotics.pdf .
