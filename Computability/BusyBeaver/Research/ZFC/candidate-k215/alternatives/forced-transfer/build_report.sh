#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
mkdir -p pdf-build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory pdf-build report.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory pdf-build report.tex
cp pdf-build/report.pdf report.pdf
