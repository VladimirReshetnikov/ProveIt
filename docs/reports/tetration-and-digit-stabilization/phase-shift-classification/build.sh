#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v pdflatex >/dev/null 2>&1 || { echo "pdflatex is not on PATH." >&2; exit 1; }
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error tetration_phase_classification.tex
done
