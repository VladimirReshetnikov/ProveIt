#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python3 verify.py --out-dir data
python3 illustrate.py
latexmk -pdf -interaction=nonstopmode -halt-on-error zigzag_spectral_research.tex
