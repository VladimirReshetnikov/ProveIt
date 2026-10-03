#!/bin/sh
set -eu
cd "$(dirname "$0")"
command -v python3 >/dev/null 2>&1 || { echo 'python3 is required.' >&2; exit 1; }
python3 code/verify_finite_checks.py
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error optimal_kummer_atlases.tex
elif command -v pdflatex >/dev/null 2>&1; then
    for pass in 1 2 3; do
        pdflatex -interaction=nonstopmode -halt-on-error optimal_kummer_atlases.tex
    done
else
    echo 'Install a TeX distribution providing pdflatex (and optionally latexmk).' >&2
    exit 1
fi
