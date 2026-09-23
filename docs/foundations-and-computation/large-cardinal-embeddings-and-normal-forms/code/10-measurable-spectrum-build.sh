#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
mkdir -p data
python3 code/finite_regression.py | tee data/finite_regression_console.txt
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
