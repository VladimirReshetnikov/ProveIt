#!/bin/sh
# Build locally with installed TeX packages; no network access is requested.
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdfLaTeX is required. Install TeX Live or MiKTeX and the packages in README.md.' >&2
    exit 1
fi
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '%s\n' 'Built article.pdf'
