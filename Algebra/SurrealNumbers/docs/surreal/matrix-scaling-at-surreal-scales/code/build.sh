#!/usr/bin/env sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$HERE"
python3 code/verify.py
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -halt-on-error -interaction=nonstopmode surreal_matrix_scaling.tex
else
    pdflatex -halt-on-error -interaction=nonstopmode surreal_matrix_scaling.tex
    pdflatex -halt-on-error -interaction=nonstopmode surreal_matrix_scaling.tex
    pdflatex -halt-on-error -interaction=nonstopmode surreal_matrix_scaling.tex
fi
