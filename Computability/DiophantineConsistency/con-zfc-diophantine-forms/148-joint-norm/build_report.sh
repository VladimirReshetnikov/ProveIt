#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 report/generate_appendix.py
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
