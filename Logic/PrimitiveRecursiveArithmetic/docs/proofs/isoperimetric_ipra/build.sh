#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
mkdir -p build
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error \
  -output-directory=build isoperimetric_ipra.tex
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error \
  -output-directory=build isoperimetric_ipra.tex
cp build/isoperimetric_ipra.pdf isoperimetric_ipra.pdf
