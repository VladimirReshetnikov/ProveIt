#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p .build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex
cp .build/article.pdf article.pdf
printf '\nBuilt article.pdf\n'
