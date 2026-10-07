#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error article.tex > build-pass1.txt
pdflatex -interaction=nonstopmode -halt-on-error article.tex > build-pass2.txt
pdflatex -interaction=nonstopmode -halt-on-error article.tex > build-pass3.txt
