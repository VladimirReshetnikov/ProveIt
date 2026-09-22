#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_physics.tex
elif command -v pdflatex >/dev/null 2>&1; then
    for pass in 1 2 3; do
        pdflatex -interaction=nonstopmode -halt-on-error surreal_physics.tex
    done
else
    printf '%s\n' 'A LaTeX installation with pdflatex is required.' >&2
    exit 1
fi
