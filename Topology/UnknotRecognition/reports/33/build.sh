#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p .build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex > .build/pass1.txt
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex > .build/pass2.txt
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex > .build/pass3.txt
cp .build/article.pdf article.pdf
printf 'Built article.pdf\n'
