#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'pdflatex was not found. Install TeX Live or MiKTeX with the packages in article.tex.' >&2
  exit 127
fi
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '\nBuilt: %s/article.pdf\n' "$PWD"
