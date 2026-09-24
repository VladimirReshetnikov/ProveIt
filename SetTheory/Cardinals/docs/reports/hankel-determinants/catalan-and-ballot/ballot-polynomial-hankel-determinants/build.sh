#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'pdflatex was not found. Install a TeX distribution first.' >&2
    exit 1
}
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
printf '%s\n' 'Built article.pdf'
