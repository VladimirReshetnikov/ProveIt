#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

python3 code/finite_clt.py --output code/validation.json

cd paper
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error central_limit_ipra.tex
else
  pdflatex -interaction=nonstopmode -halt-on-error central_limit_ipra.tex
  pdflatex -interaction=nonstopmode -halt-on-error central_limit_ipra.tex
  pdflatex -interaction=nonstopmode -halt-on-error central_limit_ipra.tex
fi
