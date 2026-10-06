#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
  echo "pdflatex is required (TeX Live or another LaTeX distribution)." >&2
  exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error fourth_order_cube_counts.tex
pdflatex -interaction=nonstopmode -halt-on-error fourth_order_cube_counts.tex
printf '\nBuilt fourth_order_cube_counts.pdf\n'
