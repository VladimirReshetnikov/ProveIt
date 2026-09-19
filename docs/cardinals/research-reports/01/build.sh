#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'pdfLaTeX is required. Install a TeX distribution with the packages listed in the source.' >&2
  exit 1
fi
for pass in 1 2; do
  printf '\nBuilding PDF, pass %s of 2...\n' "$pass"
  pdflatex -interaction=nonstopmode -halt-on-error Large_Cardinals_Continuation.tex
done
printf '\nCreated %s/Large_Cardinals_Continuation.pdf\n' "$PWD"
