#!/bin/sh
# Rebuild in the directory containing this script; no shell-escape is used.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'pdfLaTeX is required (for example, from TeX Live).' >&2
    exit 1
}
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '%s\n' 'Built article.pdf'
