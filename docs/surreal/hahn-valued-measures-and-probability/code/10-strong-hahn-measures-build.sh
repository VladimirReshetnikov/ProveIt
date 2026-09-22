#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
mkdir -p build
latexmk -pdf -outdir=build -interaction=nonstopmode -halt-on-error article.tex
cp build/article.pdf article.pdf
