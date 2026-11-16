#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1 || ! kpsewhich lmodern.sty >/dev/null 2>&1; then
  tex_runtime="$(pwd)/build/tex-runtime"
  mkdir -p "$tex_runtime"
  export TEXMF='{/etc/texmf,/usr/share/texmf,/usr/share/texlive/texmf-dist}'
  export TEXFORMATS="$tex_runtime//:"
  export TEXFONTMAPS="$tex_runtime//:"
  if [[ ! -s "$tex_runtime/pdflatex.fmt" ]]; then
    (cd "$tex_runtime" && pdftex -ini -etex -jobname=pdflatex -progname=pdflatex \
      -interaction=nonstopmode -halt-on-error pdflatex.ini > format-build.txt 2>&1)
  fi
  cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cmextra.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/latxfont.map \
      > "$tex_runtime/pdftex.map"
fi
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
    -output-directory=build report.tex > "build/pass${pass}.txt" 2>&1
done
if rg -n 'undefined references|Citation .* undefined|Reference .* undefined' build/report.log; then
  exit 1
fi
cp build/report.pdf ipra_local_global.pdf
