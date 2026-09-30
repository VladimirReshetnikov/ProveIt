#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
