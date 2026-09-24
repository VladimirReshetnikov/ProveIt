#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v latexmk >/dev/null 2>&1 || { echo 'latexmk is required.' >&2; exit 1; }
PYTHON=${PYTHON:-python3}
command -v "$PYTHON" >/dev/null 2>&1 || { echo 'Python is required.' >&2; exit 1; }
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build article.tex
cp build/article.pdf article.pdf
"$PYTHON" verify.py --output verification.json
