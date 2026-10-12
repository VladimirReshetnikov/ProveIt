#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python -m unittest discover -s tests -v
python experiments/build_tables.py
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
