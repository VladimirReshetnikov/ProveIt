#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v python3 >/dev/null 2>&1 || { echo 'Python 3.9+ is required.' >&2; exit 1; }
command -v pdflatex >/dev/null 2>&1 || { echo 'A TeX installation with pdflatex is required.' >&2; exit 1; }
python3 code/verify.py
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '\nBuilt article.pdf and data/verification_results.json.\n'
