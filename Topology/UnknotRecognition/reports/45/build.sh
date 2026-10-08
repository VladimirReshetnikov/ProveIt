#!/bin/sh
set -eu
cd "$(dirname "$0")"
python code/make_tables.py
cd docs
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
