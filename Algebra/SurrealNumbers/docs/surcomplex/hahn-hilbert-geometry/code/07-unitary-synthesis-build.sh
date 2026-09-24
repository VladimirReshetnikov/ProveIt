#!/usr/bin/env sh
set -eu
cd "$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'pdfLaTeX is required. Install TeX Live or MiKTeX.' >&2
  exit 1
}
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '%s\n' 'Built article.pdf. Run python verify.py separately for the exact diagnostics.'
