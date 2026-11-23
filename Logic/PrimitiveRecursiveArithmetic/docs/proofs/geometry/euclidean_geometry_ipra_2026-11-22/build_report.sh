#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python3 code/make_inventory.py
latexmk -pdf -halt-on-error -interaction=nonstopmode report.tex
