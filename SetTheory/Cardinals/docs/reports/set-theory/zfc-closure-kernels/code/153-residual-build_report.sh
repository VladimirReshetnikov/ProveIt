#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p .report-build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.report-build report.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.report-build report.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.report-build report.tex
cp .report-build/report.pdf report.pdf
