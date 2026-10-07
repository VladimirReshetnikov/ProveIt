#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v python3 >/dev/null || { echo 'python3 is required.' >&2; exit 1; }
command -v pdflatex >/dev/null || { echo 'pdflatex is required.' >&2; exit 1; }
python3 verify.py --output verification_results.json
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
printf '\nBuilt article.pdf and reran all exact checks.\n'
