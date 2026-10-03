#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build dfa-crossover-stabilization.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build dfa-crossover-stabilization.tex
cp build/dfa-crossover-stabilization.pdf dfa-crossover-stabilization.pdf
