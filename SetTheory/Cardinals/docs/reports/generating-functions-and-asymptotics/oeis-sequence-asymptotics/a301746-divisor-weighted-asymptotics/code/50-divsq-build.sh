#!/bin/sh
# Build in a separate directory. Normal TeX Live installations need no fallback.
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
OUT=${1:-"$HERE/build"}
mkdir -p "$OUT"
OUT=$(CDPATH= cd -- "$OUT" && pwd)
if ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXINPUTS=".:/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:${TEXINPUTS:-}"
  export TFMFONTS="/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//:${TFMFONTS:-}"
  export VFFONTS="/usr/share/texlive/texmf-dist/fonts/vf//:/usr/share/texmf/fonts/vf//:${VFFONTS:-}"
  export T1FONTS="/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//:${T1FONTS:-}"
  export ENCFONTS="/usr/share/texlive/texmf-dist/fonts/enc//:/usr/share/texmf/fonts/enc//:${ENCFONTS:-}"
  export TEXFONTMAPS="$OUT/texmf:/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//:${TEXFONTMAPS:-}"
fi
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  mkdir -p "$OUT/texmf"
  export TEXFORMATS="$OUT/texmf:${TEXFORMATS:-}"
  if [ ! -f "$OUT/texmf/pdflatex.fmt" ]; then
    pdftex -ini -etex -interaction=nonstopmode -halt-on-error \
      -jobname=pdflatex -progname=pdflatex -output-directory="$OUT/texmf" \
      '\input pdflatex.ini' > "$OUT/format-build.log"
  fi
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  mkdir -p "$OUT/texmf"
  : > "$OUT/texmf/pdftex.map"
  for map in lm.map cm.map symbols.map; do
    file=$(kpsewhich "$map" || true)
    if [ -n "$file" ]; then cat "$file" >> "$OUT/texmf/pdftex.map"; fi
  done
  export TEXFONTMAPS="$OUT/texmf:${TEXFONTMAPS:-}"
fi
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$OUT" \
    "$HERE/divisor-square-partitions.tex" > "$OUT/compile-$pass.txt"
done
printf '%s\n' "$OUT/divisor-square-partitions.pdf"
