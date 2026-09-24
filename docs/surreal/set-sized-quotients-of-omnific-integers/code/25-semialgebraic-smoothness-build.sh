#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'pdfLaTeX was not found. Install TeX Live or MiKTeX and add it to PATH.' >&2
  exit 1
fi
for pass in 1 2 3; do
  printf 'LaTeX pass %s\n' "$pass"
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '%s\n' 'Built article.pdf. Run python3 code/verify.py for the finite sanity checks.'
