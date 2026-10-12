#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python3 code/verify_exact.py --max-weight 28
python3 code/verify_numeric.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
