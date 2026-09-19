#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 code/minimal_certificate.py
python3 code/verify.py
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error delayed_digit_stabilization.tex
done
printf '%s\n' 'Built delayed_digit_stabilization.pdf'
