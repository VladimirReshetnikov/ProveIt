#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python3 code/verify.py --output data/verification.json
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
printf '\nBuilt article.pdf and refreshed finite verification results.\n'
