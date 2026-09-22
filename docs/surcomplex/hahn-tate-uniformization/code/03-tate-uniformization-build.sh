#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
    echo "pdfLaTeX was not found. Install a TeX distribution and add it to PATH." >&2
    exit 1
}
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '\nBuilt %s/article.pdf\n' "$(pwd)"
