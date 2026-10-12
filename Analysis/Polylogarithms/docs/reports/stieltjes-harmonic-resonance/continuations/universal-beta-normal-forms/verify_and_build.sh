#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python verification/check_exact.py
python verification/check_analytic.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
printf '\nVerification and PDF build completed.\n'
