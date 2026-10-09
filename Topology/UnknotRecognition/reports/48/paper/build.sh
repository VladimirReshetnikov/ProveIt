#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error article.tex > ../results/latex-pass1.txt
pdflatex -interaction=nonstopmode -halt-on-error article.tex > ../results/latex-pass2.txt
pdflatex -interaction=nonstopmode -halt-on-error article.tex > ../results/latex-final.txt
