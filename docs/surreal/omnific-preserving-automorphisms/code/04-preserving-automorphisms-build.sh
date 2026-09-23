#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error omnific_automorphisms.tex
else
  for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error omnific_automorphisms.tex
  done
fi
