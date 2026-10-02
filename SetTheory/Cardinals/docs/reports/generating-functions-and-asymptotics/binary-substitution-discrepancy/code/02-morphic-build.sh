#!/bin/sh
set -eu
mkdir -p .build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=.build article.tex
cp .build/article.pdf article.pdf
printf '%s\n' 'built article.pdf'
