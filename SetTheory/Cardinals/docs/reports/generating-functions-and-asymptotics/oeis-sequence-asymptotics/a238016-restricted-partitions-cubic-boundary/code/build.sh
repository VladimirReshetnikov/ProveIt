#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error restricted_partitions_cubic_boundary.tex
done
