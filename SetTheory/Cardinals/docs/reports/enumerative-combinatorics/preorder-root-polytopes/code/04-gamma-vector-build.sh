#!/bin/sh
# Compile the self-contained LaTeX manuscript and resolve cross-references.
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "pdflatex is required; install a TeX distribution with the preamble packages." >&2
    exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
