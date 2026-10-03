#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python code/build_examples.py
python code/verify_exports.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
