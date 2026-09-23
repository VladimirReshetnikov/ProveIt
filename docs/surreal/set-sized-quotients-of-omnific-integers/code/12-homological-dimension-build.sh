#!/bin/sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
  echo "pdfLaTeX is required; install TeX Live or an equivalent distribution." >&2
  exit 1
}
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error omnific_homological_dimension.tex
done
