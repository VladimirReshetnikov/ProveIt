#!/bin/sh
set -eu
cd "$(dirname "$0")/report"
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
cp main.pdf ../ConZFC_Symmetric_Residue_Budgets.pdf
