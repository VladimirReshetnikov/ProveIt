#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
mkdir -p .build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=.build article.tex
cp .build/article.pdf article.pdf
printf '\nBuilt article.pdf\n'
