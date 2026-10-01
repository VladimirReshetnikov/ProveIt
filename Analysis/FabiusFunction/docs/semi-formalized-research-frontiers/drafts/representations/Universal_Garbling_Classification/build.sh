#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error universal_garbling_classification.tex
done
