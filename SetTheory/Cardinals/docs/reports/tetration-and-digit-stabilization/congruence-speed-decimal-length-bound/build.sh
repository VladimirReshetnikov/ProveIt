#!/bin/sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
    echo "pdflatex is required (for example, install TeX Live)." >&2
    exit 1
}
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
printf '\nBuilt article.pdf\n'
