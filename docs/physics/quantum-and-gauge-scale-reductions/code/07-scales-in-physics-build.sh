#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=build surreal_scales_physics.tex
cp build/surreal_scales_physics.pdf surreal_scales_physics.pdf
python verify_examples.py --output verification_results.txt
