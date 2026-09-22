#!/bin/sh
# Rebuild the article and rerun the exact finite checks.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v python3 >/dev/null 2>&1; then
    printf '%s\n' 'Python 3.10+ is required for the finite verification.' >&2
    exit 1
fi
python3 verify.py
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex
elif command -v pdflatex >/dev/null 2>&1; then
    for run in 1 2 3; do
        pdflatex -halt-on-error -interaction=nonstopmode article.tex
    done
else
    printf '%s\n' 'Install a TeX distribution providing pdflatex or latexmk.' >&2
    exit 1
fi
printf '%s\n' 'PDF built. Inspect the log and rendered pages after any source changes.'
