#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mkdir -p build
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
    -output-directory=build -jobname=ipra_complexity_atlas report.tex \
    > "build/pass-${pass}.log" 2>&1
done
cp build/ipra_complexity_atlas.pdf ipra_complexity_atlas.pdf
printf '%s\n' 'Built ipra_complexity_atlas.pdf'
