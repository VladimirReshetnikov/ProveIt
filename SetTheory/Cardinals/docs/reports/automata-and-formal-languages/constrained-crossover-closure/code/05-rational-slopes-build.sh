#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build rational-rank-slopes.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build rational-rank-slopes.tex
cp build/rational-rank-slopes.pdf rational-rank-slopes.pdf
