#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'pdfLaTeX is required; install a suitable TeX distribution.' >&2
  exit 1
fi
if ! command -v python3 >/dev/null 2>&1; then
  printf '%s\n' 'Python 3.10 or later is required for the finite checks.' >&2
  exit 1
fi
for run in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error surcomplex_gamma_zeta.tex
done
python3 checks/verify.py
