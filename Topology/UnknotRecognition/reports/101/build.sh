#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error article.tex > results/latex_pass1.txt
pdflatex -interaction=nonstopmode -halt-on-error article.tex > results/latex_pass2.txt
pdflatex -interaction=nonstopmode -halt-on-error article.tex > results/latex_pass3.txt
