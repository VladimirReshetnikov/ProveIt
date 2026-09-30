#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 code/verify.py
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex
done
cp build/article.pdf article.pdf
printf '\nBuilt article.pdf; verification_results.json refreshed.\n'
