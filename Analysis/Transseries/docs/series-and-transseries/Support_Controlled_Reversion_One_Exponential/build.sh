#!/bin/sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'pdfLaTeX is required; install a standard TeX distribution.' >&2
  exit 1
}
for pass in 1 2 3; do
  printf '\nPDF build pass %s of 3\n' "$pass"
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
    reversion_and_one_exponential.tex
done
