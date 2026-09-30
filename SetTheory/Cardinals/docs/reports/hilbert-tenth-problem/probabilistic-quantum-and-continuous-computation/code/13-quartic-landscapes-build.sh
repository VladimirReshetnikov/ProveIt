#!/bin/sh
# Rebuild references and the two-page table of contents.
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo 'pdflatex is required; install a TeX distribution with the article packages.' >&2
    exit 1
fi
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '\nBuilt: %s/article.pdf\n' "$PWD"
