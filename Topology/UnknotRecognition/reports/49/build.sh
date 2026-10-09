#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B experiments/make_tables.py
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
