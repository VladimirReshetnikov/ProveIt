#!/bin/sh
# Compile the self-contained LaTeX article and resolve cross-references.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "pdflatex not found; install a TeX distribution such as TeX Live." >&2
    exit 1
fi
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
printf '\nBuilt %s/article.pdf\n' "$(pwd)"
