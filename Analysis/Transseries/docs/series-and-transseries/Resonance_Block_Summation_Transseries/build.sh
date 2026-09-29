#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
python verify.py --stage all
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex > "build_pass_${pass}.txt"
done
printf '%s\n' 'Built article.pdf and refreshed results/. See article.log for TeX diagnostics.'
