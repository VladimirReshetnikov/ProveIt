#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'pdflatex is required (TeX Live or MiKTeX).' >&2
  exit 1
fi
for pass in 1 2 3; do
  printf 'LaTeX pass %s/3\n' "$pass"
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
if grep -Eq 'undefined references|Citation .* undefined|Reference .* undefined' article.log; then
  printf '%s\n' 'Unresolved references remain; inspect article.log.' >&2
  exit 1
fi
printf '%s\n' 'Built article.pdf'
