#!/bin/sh
# Compile from the directory containing this script. No shell escape is used.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdfLaTeX is required. Install TeX Live or MiKTeX.' >&2
    exit 127
fi
for run in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        omnific_differential_rigidity.tex
done
printf '%s\n' 'Built omnific_differential_rigidity.pdf'
