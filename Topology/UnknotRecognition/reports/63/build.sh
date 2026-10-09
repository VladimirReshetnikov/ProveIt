#!/bin/sh
set -eu
cd "$(dirname "$0")"
python make_tables.py
mkdir -p docs/build
cd docs
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > build/pass1.txt
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > build/pass2.txt
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > build/pass3.txt
cp build/article.pdf article.pdf
printf '%s\n' 'Built docs/article.pdf'
