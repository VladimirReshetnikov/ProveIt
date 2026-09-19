#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify.py
python3 minimal_verifier.py
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "pdflatex is required to build the article PDF." >&2
    exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
printf '\nBuilt article.pdf. Optional symbolic audit: python3 derive_symbolic.py\n'
