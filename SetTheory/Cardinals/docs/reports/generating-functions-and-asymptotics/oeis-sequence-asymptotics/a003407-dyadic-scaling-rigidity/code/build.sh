#!/bin/sh
# Build from any working directory; the packaged figure is sufficient.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdfLaTeX is required. Install a LaTeX distribution first.' >&2
    exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
