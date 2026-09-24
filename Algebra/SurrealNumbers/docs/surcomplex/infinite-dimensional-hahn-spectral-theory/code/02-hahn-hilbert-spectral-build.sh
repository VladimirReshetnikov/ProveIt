#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p data
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
python3 -u code/verify.py | tee data/verification.txt
