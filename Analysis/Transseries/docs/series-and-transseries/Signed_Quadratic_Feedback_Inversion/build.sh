#!/bin/sh
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "pdflatex was not found. Install a TeX distribution with the packages listed in article.tex." >&2
    exit 1
fi
# Repeated passes settle the table of contents, citations, and cross-references.
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
