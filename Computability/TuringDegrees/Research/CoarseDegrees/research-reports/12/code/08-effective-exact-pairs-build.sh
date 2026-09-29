#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python3 code/verify.py --output data/verification.json
for run in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error article.tex >/dev/null
done
printf '%s\n' 'Built article.pdf; finite verification output is data/verification.json.'
