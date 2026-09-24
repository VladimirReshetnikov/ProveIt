#!/bin/sh
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdflatex is required. Install a LaTeX distribution such as TeX Live or MiKTeX.' >&2
    exit 1
fi
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '%s\n' 'Built article.pdf.'
