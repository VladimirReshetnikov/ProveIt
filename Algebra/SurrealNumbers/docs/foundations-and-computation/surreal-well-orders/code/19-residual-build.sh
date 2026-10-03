#!/usr/bin/env sh
set -eu
cd -- "$(dirname -- "$0")"
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_lexicographic_orders_continuation.tex
else
    pdflatex -interaction=nonstopmode -halt-on-error surreal_lexicographic_orders_continuation.tex
    pdflatex -interaction=nonstopmode -halt-on-error surreal_lexicographic_orders_continuation.tex
    pdflatex -interaction=nonstopmode -halt-on-error surreal_lexicographic_orders_continuation.tex
fi
