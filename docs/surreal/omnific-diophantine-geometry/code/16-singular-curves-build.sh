#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
else
  for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
  done
fi
