#!/bin/sh
set -eu
cd "$(dirname "$0")"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error lower_critical_endpoint.tex > "build-pass-${pass}.log"
done
printf '%s\n' 'Built lower_critical_endpoint.pdf'
