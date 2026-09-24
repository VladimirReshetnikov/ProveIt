#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "pdfLaTeX was not found. Install TeX Live or MiKTeX and add it to PATH." >&2
    exit 1
fi
for pass in 1 2 3; do
    echo "pdfLaTeX pass $pass"
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '\nCreated article.pdf\n'
