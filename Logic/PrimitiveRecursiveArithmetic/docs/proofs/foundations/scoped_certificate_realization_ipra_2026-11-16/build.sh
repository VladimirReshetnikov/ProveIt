#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"

cd "$ROOT/reference"
python3 -m unittest -v test_scr_reference.py |& tee "$ROOT/validation/python_tests.txt"
python3 scr_reference.py > "$ROOT/examples/demo.json"

cd "$ROOT/paper"
latexmk -pdf -interaction=nonstopmode -halt-on-error scr_ipra_framework.tex
pdfinfo scr_ipra_framework.pdf > "$ROOT/validation/pdfinfo.txt"

echo "Build complete: $ROOT/paper/scr_ipra_framework.pdf"
