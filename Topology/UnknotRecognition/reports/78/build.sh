#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 scripts/build_article.py
cd article
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
