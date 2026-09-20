#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error article.tex
if command -v bibtex >/dev/null 2>&1; then
    bibtex article
elif command -v bibtex8 >/dev/null 2>&1; then
    bibtex8 article
else
    echo "A BibTeX executable (bibtex or bibtex8) is required." >&2
    exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
