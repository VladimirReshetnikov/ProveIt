#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
python3 src/verify_all.py
pdflatex -interaction=nonstopmode -halt-on-error zfc_diophantine.tex
pdflatex -interaction=nonstopmode -halt-on-error zfc_diophantine.tex
