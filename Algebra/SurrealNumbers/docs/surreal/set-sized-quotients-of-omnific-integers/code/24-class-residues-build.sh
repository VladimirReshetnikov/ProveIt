#!/usr/bin/env bash
set -euo pipefail
here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$here"
command -v pdflatex >/dev/null || { echo "pdfLaTeX is required." >&2; exit 1; }
command -v python3 >/dev/null || { echo "Python 3.9+ is required." >&2; exit 1; }
mkdir -p .build
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex
done
cp .build/article.pdf article.pdf
python3 code/verify.py
printf '\nBuilt: %s/article.pdf\n' "$here"
