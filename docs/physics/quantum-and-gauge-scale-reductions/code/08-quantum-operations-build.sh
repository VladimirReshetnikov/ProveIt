#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 code/verify.py
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex
else
    for pass in 1 2 3; do
        pdflatex -halt-on-error -interaction=nonstopmode article.tex
    done
fi
