#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2 3; do
 pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build exact_fabius_mask_order.tex > "build/pass-$pass.log"
done
cp build/exact_fabius_mask_order.pdf .
