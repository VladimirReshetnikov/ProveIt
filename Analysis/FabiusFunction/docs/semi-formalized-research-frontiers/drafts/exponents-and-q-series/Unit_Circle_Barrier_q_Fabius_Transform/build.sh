#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'pdflatex is required; install a TeX Live distribution.' >&2
  exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error q_fabius_boundary.tex
pdflatex -interaction=nonstopmode -halt-on-error q_fabius_boundary.tex
