#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 verify.py
for i in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error detector.tex >/dev/null; done
printf 'Built detector.pdf\n'
