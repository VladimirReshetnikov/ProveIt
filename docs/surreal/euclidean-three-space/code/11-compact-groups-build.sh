#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
