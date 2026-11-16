#!/usr/bin/env bash
set -euo pipefail
bell_package_dir="$(cd "$(dirname "$0")" && pwd)"
cd "$bell_package_dir/paper"
for bell_pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error bell_ipra.tex
done
