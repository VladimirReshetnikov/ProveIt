#!/bin/sh
set -eu
cd "$(dirname "$0")"
name=surreal_polytopes_contact_depth
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error "$name.tex"
elif command -v pdflatex >/dev/null 2>&1; then
    pdflatex -interaction=nonstopmode -halt-on-error "$name.tex"
    pdflatex -interaction=nonstopmode -halt-on-error "$name.tex"
    pdflatex -interaction=nonstopmode -halt-on-error "$name.tex"
else
    printf '%s\n' 'Install TeX Live (or another distribution providing pdflatex).' >&2
    exit 1
fi
