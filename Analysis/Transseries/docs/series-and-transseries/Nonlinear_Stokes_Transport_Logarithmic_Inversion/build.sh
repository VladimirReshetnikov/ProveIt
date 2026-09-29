#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python verify.py --out results
python make_figure.py
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex > "build-pass-${pass}.log"
done
printf 'Built article.pdf; verification results in results/\n'
