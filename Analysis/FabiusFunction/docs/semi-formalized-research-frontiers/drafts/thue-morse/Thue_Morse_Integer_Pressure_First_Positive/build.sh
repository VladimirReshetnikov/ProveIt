#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2 3; do
 pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build positive_thue_morse_coefficient.tex > "build/pass-$pass.log"
done
cp build/positive_thue_morse_coefficient.pdf .
