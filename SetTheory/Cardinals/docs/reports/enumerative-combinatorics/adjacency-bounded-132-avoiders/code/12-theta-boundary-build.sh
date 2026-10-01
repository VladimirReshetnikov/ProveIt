#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build theta_avoider_boundary.tex > "build/pass-$pass.stdout"
done
cp build/theta_avoider_boundary.pdf .
