#!/bin/sh
# Rebuild the article from the package root; three passes stabilize all references.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
    echo 'pdfLaTeX is required (install a suitable TeX Live distribution).' >&2
    exit 1
}
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
