#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v python3 >/dev/null 2>&1; then
  echo "Python 3.10+ is required for the regression checks." >&2
  exit 1
fi
python3 code/finite_checks.py
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
elif command -v pdflatex >/dev/null 2>&1; then
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
else
  echo "Install a TeX distribution with pdflatex and the preamble packages." >&2
  exit 1
fi
