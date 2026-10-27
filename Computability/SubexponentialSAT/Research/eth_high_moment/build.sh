#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2 3; do
  pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error \
    -output-directory build report.tex > "build/pass-${pass}.txt"
done
cp build/report.pdf report.pdf
echo "Built report.pdf"

