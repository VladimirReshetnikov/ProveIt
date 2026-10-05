#!/usr/bin/env sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
else
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
fi
