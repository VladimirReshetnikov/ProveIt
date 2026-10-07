#!/bin/sh
set -eu
cd "$(dirname "$0")"
python docs/build_tables.py
cd docs
pdflatex -interaction=nonstopmode -halt-on-error article.tex > build-pass1.log
pdflatex -interaction=nonstopmode -halt-on-error article.tex > build-pass2.log
pdflatex -interaction=nonstopmode -halt-on-error article.tex > build-pass3.log
printf 'Built docs/article.pdf\n'
