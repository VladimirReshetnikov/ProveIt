#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 code/finite_checks.py --output data/finite_checks.json
pdflatex -interaction=nonstopmode -halt-on-error article.tex >/dev/null
pdflatex -interaction=nonstopmode -halt-on-error article.tex >/dev/null
pdflatex -interaction=nonstopmode -halt-on-error article.tex >/dev/null
printf 'Built article.pdf and refreshed exact finite checks.\n'
