#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python3 code/verify.py --output results
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error signed_binomial_supercongruence.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error signed_binomial_supercongruence.tex
printf '\nBuilt signed_binomial_supercongruence.pdf and regenerated results.\n'
