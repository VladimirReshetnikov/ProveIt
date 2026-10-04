#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"

if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error -no-shell-escape \
    polish_completions_class_manifolds.tex
else
  for article_pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape \
      polish_completions_class_manifolds.tex
  done
fi
