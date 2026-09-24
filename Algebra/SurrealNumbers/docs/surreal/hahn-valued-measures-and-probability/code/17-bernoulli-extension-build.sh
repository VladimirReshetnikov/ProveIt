#!/usr/bin/env bash
# Build the article and run its finite verification suite.
set -euo pipefail
cd -- "$(dirname -- "$0")"
command -v python3 >/dev/null || { echo 'python3 is required.' >&2; exit 1; }
command -v pdflatex >/dev/null || { echo 'pdflatex is required.' >&2; exit 1; }
python3 code/verify.py
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '\nBuilt article.pdf. The Python checks cover finite identities only.\n'
