#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify.py
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex > "build-pass-$pass.log"
done
printf '%s\n' 'Built article.pdf; finite-check reports are verification.json and verification.txt.'
