#!/bin/sh
# Rebuild the verification report and the article from this directory.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v python3 >/dev/null 2>&1; then
  echo "Python 3.10 or later is required for the finite checks." >&2
  exit 1
fi
python3 verify.py
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error omnific_set_shadows.tex
elif command -v pdflatex >/dev/null 2>&1; then
  for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error omnific_set_shadows.tex
  done
else
  echo "Install a TeX distribution with pdflatex (and preferably latexmk)." >&2
  exit 1
fi
