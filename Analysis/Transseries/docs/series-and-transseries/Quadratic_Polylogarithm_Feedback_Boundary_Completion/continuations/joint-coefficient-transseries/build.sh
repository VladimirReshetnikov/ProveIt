#!/usr/bin/env bash
set -euo pipefail
proveit_package_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$proveit_package_dir"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error article.tex
else
  for proveit_tex_pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error article.tex
  done
fi
