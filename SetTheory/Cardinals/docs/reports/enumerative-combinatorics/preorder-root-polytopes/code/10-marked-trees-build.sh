#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "pdfLaTeX is required; install a TeX distribution with the packages in article.tex." >&2
    exit 1
fi
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex
 done
cp build/article.pdf article.pdf
printf '\nBuilt article.pdf\n'
