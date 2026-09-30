#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
    -output-directory=build triangular_hahn_systems.tex > "build/pass-${pass}.txt"
done
cp build/triangular_hahn_systems.pdf triangular_hahn_systems.pdf
printf '%s\n' 'Built triangular_hahn_systems.pdf'
