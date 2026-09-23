#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python3 verification.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
