#!/bin/sh
# Regenerate tables from data/ and ../fast/results, then build report.pdf (pdflatex twice).
set -e
cd "$(dirname "$0")"
python make_tables.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
