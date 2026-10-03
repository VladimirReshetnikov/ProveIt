#!/bin/sh
# Compile supplied sources; optional numerical verification is separate.
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
    echo "pdflatex not found. Install a standard TeX Live or MiKTeX distribution." >&2
    exit 1
}
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
