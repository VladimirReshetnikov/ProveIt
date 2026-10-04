#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
command -v python3 >/dev/null 2>&1 || { echo 'Python 3.10+ is required.' >&2; exit 1; }
command -v latexmk >/dev/null 2>&1 || { echo 'latexmk and a TeX installation are required.' >&2; exit 1; }
python3 validate.py
latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_self_embeddings.tex
