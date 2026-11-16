#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/paper"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error barnes_g_ipra.tex > "../evidence/pdf_build_pass${pass}.txt"
done
