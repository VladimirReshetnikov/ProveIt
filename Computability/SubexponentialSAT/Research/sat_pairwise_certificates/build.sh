#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error report.tex > results/latex_first.log
pdflatex -interaction=nonstopmode -halt-on-error report.tex > results/latex_second.log
pdflatex -interaction=nonstopmode -halt-on-error report.tex > results/latex_final.log
echo 'Built report.pdf'
