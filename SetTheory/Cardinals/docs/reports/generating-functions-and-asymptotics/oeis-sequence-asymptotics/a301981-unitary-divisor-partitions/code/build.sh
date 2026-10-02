#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p .build
if [[ -z "${TEXMF:-}" ]] && [[ -d /usr/share/texlive/texmf-dist ]] && ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
fi
export TEXMFVAR="$PWD/.build"
export TEXMFCONFIG="$PWD/.build"
export TEXFORMATS="$PWD/.build:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd .build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini > format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : > .build/pdftex.map
  for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
    map=$(kpsewhich "$name") || { echo "Missing font map $name" >&2; exit 1; }
    cat "$map" >> .build/pdftex.map
  done
  export TEXFONTMAPS="$PWD/.build:"
fi
export SOURCE_DATE_EPOCH=1790899200
export FORCE_SOURCE_DATE=1
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build unitary-partitions.tex > ".build/compile-$pass.log"
done
cp .build/unitary-partitions.pdf unitary-partitions.pdf
printf 'Built %s\n' "$PWD/unitary-partitions.pdf"
