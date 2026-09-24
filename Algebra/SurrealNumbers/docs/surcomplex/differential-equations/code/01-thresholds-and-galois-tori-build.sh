#!/bin/sh
# Reproduce finite checks and build the PDF. No installations or network access.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if command -v python3 >/dev/null 2>&1; then
    python3 code/verify.py
elif command -v python >/dev/null 2>&1; then
    python code/verify.py
else
    echo "Python 3.9 or later is required." >&2
    exit 1
fi
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
elif command -v pdflatex >/dev/null 2>&1; then
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
else
    echo "A TeX installation with latexmk or pdflatex is required." >&2
    exit 1
fi
