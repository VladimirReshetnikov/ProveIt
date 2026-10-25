#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B code/report_inputs.py --check
cd report
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
cp main.pdf ../ConZFC_Trace_Radical_2026-10-25.pdf
