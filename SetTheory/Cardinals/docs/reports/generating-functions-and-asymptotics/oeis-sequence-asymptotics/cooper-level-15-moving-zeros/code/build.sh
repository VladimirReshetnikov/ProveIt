#!/usr/bin/env bash
# Offline build with a standard TeX Live installation and pdfLaTeX.
# No package downloads are performed. The fallback handles an installed TeX tree
# whose generated filename database, format, or font map is absent.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
export SOURCE_DATE_EPOCH=1790899200
export FORCE_SOURCE_DATE=1
export TZ=UTC
export LC_ALL=C
command -v pdflatex >/dev/null || { echo 'pdfLaTeX is required.' >&2; exit 1; }
mkdir -p .build/texmf-var .build/texmf-config
export TEXMFVAR="$PWD/.build/texmf-var"
export TEXMFCONFIG="$PWD/.build/texmf-config"
if ! kpsewhich article.cls >/dev/null 2>&1; then
  if [[ -d /usr/share/texlive/texmf-dist ]]; then
    export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
  else
    echo 'The installed LaTeX classes are not discoverable.' >&2; exit 1
  fi
fi
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1 && [[ ! -f .build/pdflatex.fmt ]]; then
  pdflatex -ini -interaction=nonstopmode -halt-on-error -jobname=pdflatex \
    -output-directory=.build '*pdflatex.ini' >.build/format-build.log 2>&1
fi
export TEXFORMATS="$PWD/.build:"
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : > .build/pdftex.map
  for map in lm.map cm.map cmextra.map symbols.map latxfont.map; do
    path="$(kpsewhich "$map")" || { echo "Missing font map: $map" >&2; exit 1; }
    cat "$path" >> .build/pdftex.map
  done
  export TEXFONTMAPS="$PWD/.build:"
fi
source=modular-crossover.tex
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
    -output-directory=.build "$source" >".build/build-pass-$pass.log" 2>&1
done
cp ".build/${source%.tex}.pdf" "${source%.tex}.pdf"
printf 'Built %s/%s.pdf\n' "$PWD" "${source%.tex}"
