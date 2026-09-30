#!/bin/sh
set -eu
cd "$(dirname "$0")"
PYTHON="${PYTHON:-python3}"
command -v "$PYTHON" >/dev/null 2>&1 || { echo "Python interpreter not found: $PYTHON" >&2; exit 1; }
command -v pdflatex >/dev/null 2>&1 || { echo "pdflatex is required." >&2; exit 1; }
mkdir -p build
"$PYTHON" verify.py --outdir build/results
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > "build/latex-pass-$pass.txt" 2>&1; then
        tail -60 "build/latex-pass-$pass.txt" >&2
        exit 1
    fi
done
cp build/article.pdf article.pdf
printf '%s\n' "Built article.pdf. Recomputed diagnostics are in build/results/."
