#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 code/verify_formulas.py
python3 code/make_figures.py
latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
