#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'pdflatex is required (for example, a TeX Live installation).' >&2
  exit 1
}
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '%s\n' 'Built article.pdf'
