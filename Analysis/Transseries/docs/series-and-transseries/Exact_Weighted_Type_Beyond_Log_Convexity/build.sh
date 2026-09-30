#!/bin/sh
set -eu
cd "$(dirname "$0")"
"${PYTHON:-python3}" code/verify.py --order 36 --output build/verification
for pass in 1 2 3; do
    "${PDFLATEX:-pdflatex}" -interaction=nonstopmode -halt-on-error article.tex
done
