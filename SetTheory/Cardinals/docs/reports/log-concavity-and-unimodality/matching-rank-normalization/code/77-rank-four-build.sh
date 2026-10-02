#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build matching-rank-four.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build matching-rank-four.tex
cp build/matching-rank-four.pdf matching-rank-four.pdf
