#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python3 verify_finite.py
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_well_orders.tex
else
  pdflatex -interaction=nonstopmode -halt-on-error surreal_well_orders.tex
  pdflatex -interaction=nonstopmode -halt-on-error surreal_well_orders.tex
  pdflatex -interaction=nonstopmode -halt-on-error surreal_well_orders.tex
fi
