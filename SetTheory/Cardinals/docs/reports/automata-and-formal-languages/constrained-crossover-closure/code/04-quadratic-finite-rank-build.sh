#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build quadratic-finite-rank.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build quadratic-finite-rank.tex
cp build/quadratic-finite-rank.pdf quadratic-finite-rank.pdf
