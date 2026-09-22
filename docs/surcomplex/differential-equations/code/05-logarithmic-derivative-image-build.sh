#!/usr/bin/env sh
# Build the standalone article. Does not invoke shell escape or fetch packages.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
elif command -v pdflatex >/dev/null 2>&1; then
    for pass in 1 2 3; do
        pdflatex -interaction=nonstopmode -halt-on-error article.tex
    done
else
    printf '%s\n' 'A LaTeX installation with pdfLaTeX is required.' >&2
    exit 1
fi
