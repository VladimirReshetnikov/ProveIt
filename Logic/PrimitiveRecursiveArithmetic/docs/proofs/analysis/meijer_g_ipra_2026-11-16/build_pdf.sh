#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"
python3 code/generate_coverage_table.py
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error meijer_g_ipra.tex
cp meijer_g_ipra.pdf ..
