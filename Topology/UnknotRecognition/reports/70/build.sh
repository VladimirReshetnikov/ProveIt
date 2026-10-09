#!/bin/sh
set -eu
cd "$(dirname "$0")"
python scripts/make_tables.py
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
