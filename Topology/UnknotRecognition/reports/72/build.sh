#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p results
python3 -m experiments.make_tables
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex > "results/build_pass${pass}.log" 2>&1
done
printf '%s\n' 'Built article.pdf; logs are in results/.'
