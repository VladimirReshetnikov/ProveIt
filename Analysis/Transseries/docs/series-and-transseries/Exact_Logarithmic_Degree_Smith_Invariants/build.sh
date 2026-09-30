#!/bin/sh
set -eu
cd "$(dirname "$0")"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error exact_logarithmic_degree.tex > "build-pass-${pass}.log"
done
printf '%s\n' 'Built exact_logarithmic_degree.pdf'
