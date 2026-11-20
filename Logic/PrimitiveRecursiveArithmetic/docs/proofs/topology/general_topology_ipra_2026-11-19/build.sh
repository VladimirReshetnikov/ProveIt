#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/paper"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error main.tex > "../validation/latex-pass-${pass}.log" 2>&1
done
cp -- main.pdf ../general_topology_ipra.pdf

