#!/bin/sh
# Rebuild in place. Requires Python 3.10+ and a standard pdfLaTeX distribution.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v python3 >/dev/null 2>&1 || { echo 'python3 is required' >&2; exit 1; }
command -v pdflatex >/dev/null 2>&1 || { echo 'pdflatex is required' >&2; exit 1; }
python3 verify.py
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '\nBuilt article.pdf; finite-check results are in verification.json.\n'
