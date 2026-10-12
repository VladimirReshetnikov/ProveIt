#!/bin/sh
set -eu
cd "$(dirname "$0")"
python -m unittest discover -s tests -v
python experiments/build_tables.py
python experiments/inline_article.py
cd article
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
