#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p .build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build order_free_diophantine.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build order_free_diophantine.tex
cp .build/order_free_diophantine.pdf order_free_diophantine.pdf
