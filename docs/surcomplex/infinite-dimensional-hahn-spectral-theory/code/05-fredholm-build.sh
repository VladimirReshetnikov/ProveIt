#!/usr/bin/env bash
# Build the standalone article; optionally run the exact finite checks.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
export TERM="${TERM:-dumb}"
if [[ $# -gt 1 ]] || [[ $# -eq 1 && "$1" != "--verify" ]]; then
  printf 'Usage: %s [--verify]\n' "$0" >&2
  exit 2
fi
mkdir -p data
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex
elif command -v pdflatex >/dev/null 2>&1; then
  for pass in 1 2 3; do
    pdflatex -halt-on-error -interaction=nonstopmode article.tex
  done
else
  printf 'Install a TeX distribution providing latexmk or pdflatex.\n' >&2
  exit 1
fi
if [[ $# -eq 1 ]]; then
  python3 code/verify.py --output data/verification.json
fi
printf '\nBuilt %s/article.pdf\n' "$PWD"
