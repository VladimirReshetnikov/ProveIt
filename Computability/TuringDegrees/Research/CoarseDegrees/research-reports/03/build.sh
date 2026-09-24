#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
python3 code/check_finite.py
pdflatex -interaction=nonstopmode -halt-on-error coarse_counterexample.tex
pdflatex -interaction=nonstopmode -halt-on-error coarse_counterexample.tex
pdflatex -interaction=nonstopmode -halt-on-error coarse_counterexample.tex
