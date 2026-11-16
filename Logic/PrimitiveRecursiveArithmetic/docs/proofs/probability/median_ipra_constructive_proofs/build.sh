#!/usr/bin/env sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
python3 "$ROOT/code/median_ipra_reference.py" \
  --output "$ROOT/code/validation.json" >/dev/null
cd "$ROOT/paper"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error median_ipra.tex
else
  pdflatex -interaction=nonstopmode -halt-on-error median_ipra.tex
  pdflatex -interaction=nonstopmode -halt-on-error median_ipra.tex
  pdflatex -interaction=nonstopmode -halt-on-error median_ipra.tex
fi
