#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p .build
if ! command -v pdflatex >/dev/null || ! command -v kpsewhich >/dev/null; then
  printf 'A TeX distribution with pdfLaTeX is required.\n' >&2; exit 1
fi
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1 || ! kpsewhich pdftex.map >/dev/null 2>&1; then
  export TEXMF="$(kpsewhich -var-value=TEXMF | sed 's/!!//g')"
  export TEXMFVAR="$PWD/.build/texmf-var"
  export TEXMFCONFIG="$PWD/.build/texmf-config"
  export TEXMFCACHE="$PWD/.build/texmf-cache"
  export TEXFORMATS="$PWD/.build:"
  if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
    (cd .build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini > format-build.log)
  fi
  if ! kpsewhich pdftex.map >/dev/null 2>&1; then
    : > .build/pdftex.map
    for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
      map="$(kpsewhich "$name")"; cat "$map" >> .build/pdftex.map
    done
    export TEXFONTMAPS="$PWD/.build:"
  fi
fi
for pass in 1 2 3; do
 pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build d-combining-asymptotics.tex > .build/compile-$pass.log
done
cp .build/d-combining-asymptotics.pdf d-combining-asymptotics.pdf
printf 'Built d-combining-asymptotics.pdf\n'
