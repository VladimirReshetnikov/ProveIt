#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build report.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build report.tex
cp build/report.pdf report.pdf
