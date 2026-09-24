#!/usr/bin/env sh
# Two-pass PDF build. `latexmk -pdf article.tex` is equivalent and preferred.
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdflatex was not found. Install a TeX distribution first.' >&2
    exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
printf '\nBuilt article.pdf\n'
