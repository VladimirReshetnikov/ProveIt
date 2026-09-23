#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'pdfLaTeX is required; install a LaTeX distribution before building.' >&2
  exit 1
fi
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '%s\n' 'Built article.pdf. Run python3 verify.py separately for the exact finite checks.'
