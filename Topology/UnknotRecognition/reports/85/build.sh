#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
for pass in 1 2 3; do
  pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -file-line-error article.tex
done
