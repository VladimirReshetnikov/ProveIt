#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build wasserstein-resonance.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build wasserstein-resonance.tex
cp build/wasserstein-resonance.pdf wasserstein-resonance.pdf
