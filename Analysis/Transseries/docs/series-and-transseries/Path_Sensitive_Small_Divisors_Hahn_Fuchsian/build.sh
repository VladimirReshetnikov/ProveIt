#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build path_sensitive_hahn.tex > "build/pass-$pass.txt"
done
cp build/path_sensitive_hahn.pdf path_sensitive_hahn.pdf
printf '%s\n' 'Built path_sensitive_hahn.pdf'
