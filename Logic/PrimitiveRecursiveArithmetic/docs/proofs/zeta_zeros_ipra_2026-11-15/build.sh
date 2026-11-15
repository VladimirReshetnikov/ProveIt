#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python3 code/rational_zeta.py
python3 code/good_height_bounds.py > verification/bounds_examples.json
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build zeta_zeros_ipra.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build zeta_zeros_ipra.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build zeta_zeros_ipra.tex
cp build/zeta_zeros_ipra.pdf zeta_zeros_ipra.pdf
