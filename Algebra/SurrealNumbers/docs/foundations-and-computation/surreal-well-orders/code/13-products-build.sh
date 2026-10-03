#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
command -v pdflatex >/dev/null || { echo "pdflatex is required (TeX Live recommended)." >&2; exit 1; }
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex > "build-pass-${pass}.log"
done
printf 'Built %s/article.pdf\n' "$PWD"
