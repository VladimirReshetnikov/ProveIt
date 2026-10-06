#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 verify.py
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex >/dev/null
done
printf 'Built article.pdf and refreshed verification_results.json\n'
