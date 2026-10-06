#!/bin/sh
set -eu
cd "$(dirname "$0")"
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error gowers_refinements.tex
elif command -v pdflatex >/dev/null 2>&1; then
    for pass in 1 2 3; do
        pdflatex -interaction=nonstopmode -halt-on-error gowers_refinements.tex
    done
else
    echo 'Install a TeX distribution providing latexmk or pdflatex.' >&2
    exit 1
fi
