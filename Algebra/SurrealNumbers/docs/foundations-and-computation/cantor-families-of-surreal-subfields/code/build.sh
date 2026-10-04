#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python3 code/finite_checks.py --output data/finite_checks.json
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
