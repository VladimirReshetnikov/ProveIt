#!/usr/bin/env sh
set -eu
cd -- "$(dirname -- "$0")"
if command -v latexmk >/dev/null 2>&1; then
    exec latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
fi
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
