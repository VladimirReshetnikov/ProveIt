#!/usr/bin/env bash
# Build the self-contained article; requires a LaTeX installation and latexmk.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build surreal_numbers_black_holes.tex
cp build/surreal_numbers_black_holes.pdf surreal_numbers_black_holes.pdf
printf '\nBuilt surreal_numbers_black_holes.pdf\n'
