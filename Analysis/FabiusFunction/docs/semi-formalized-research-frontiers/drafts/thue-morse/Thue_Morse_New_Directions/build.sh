#!/bin/sh
# Build the self-contained article from this directory.
set -eu
cd "$(dirname "$0")"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error thue_morse_new_directions.tex
else
  for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error thue_morse_new_directions.tex
  done
fi
