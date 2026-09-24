#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
name=Small_Fibres_Ultraexacting.tex
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error "$name"
else
    command -v pdflatex >/dev/null 2>&1 || {
        printf '%s\n' 'pdfLaTeX was not found. Install TeX Live or MiKTeX and the packages listed in README.md.' >&2
        exit 1
    }
    for pass in 1 2 3; do
        pdflatex -interaction=nonstopmode -halt-on-error "$name"
    done
fi
