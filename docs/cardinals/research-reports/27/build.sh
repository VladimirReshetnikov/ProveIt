#!/bin/sh
set -eu
cd "$(dirname "$0")"
SOURCE=Normal_Traces_and_Prikry_Factorization.tex
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error "$SOURCE"
elif command -v pdflatex >/dev/null 2>&1; then
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error "$SOURCE"
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error "$SOURCE"
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error "$SOURCE"
else
    printf '%s\n' 'Install a TeX distribution with pdfLaTeX and the packages listed in README.md.' >&2
    exit 1
fi
