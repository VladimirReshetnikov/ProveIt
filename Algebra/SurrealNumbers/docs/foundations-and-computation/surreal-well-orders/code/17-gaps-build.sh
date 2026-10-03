#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 finite_checks.py --output finite_checks.json
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
