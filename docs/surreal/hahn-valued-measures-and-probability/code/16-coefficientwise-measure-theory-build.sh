#!/bin/sh
set -eu
cd "$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)"
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -halt-on-error -interaction=nonstopmode surreal_measure_theory.tex
elif command -v pdflatex >/dev/null 2>&1; then
    for pass in 1 2 3; do
        pdflatex -halt-on-error -interaction=nonstopmode surreal_measure_theory.tex
    done
else
    printf '%s\n' 'A TeX distribution with pdflatex is required.' >&2
    exit 1
fi
if ! command -v python3 >/dev/null 2>&1; then
    printf '%s\n' 'Python 3.10 or later is required for the finite checks.' >&2
    exit 1
fi
python3 verify_examples.py --output verification_results.json
