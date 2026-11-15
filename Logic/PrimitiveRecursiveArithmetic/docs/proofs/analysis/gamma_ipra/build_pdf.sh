#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")/paper"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape gamma_ipra.tex
done
