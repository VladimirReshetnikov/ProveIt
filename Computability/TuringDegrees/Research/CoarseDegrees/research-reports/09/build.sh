#!/bin/sh
set -eu
cd "$(dirname "$0")"
if command -v python3 >/dev/null 2>&1; then
    PYTHON=python3
elif command -v python >/dev/null 2>&1; then
    PYTHON=python
else
    echo "Python 3.9 or later is required." >&2
    exit 1
fi
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "pdflatex is required (TeX Live or MiKTeX)." >&2
    exit 1
fi
"$PYTHON" checks/check_finite_lemmas.py --output checks/results.json
mkdir -p _build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=_build coarse_degree_attack.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=_build coarse_degree_attack.tex
cp _build/coarse_degree_attack.pdf coarse_degree_attack.pdf
printf '\nBuilt coarse_degree_attack.pdf\n'
