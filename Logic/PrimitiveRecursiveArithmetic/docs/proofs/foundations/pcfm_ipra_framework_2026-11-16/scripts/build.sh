#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$ROOT/metadata"

echo "[1/4] Python unit tests"
python3 -m unittest discover -s "$ROOT/tests" -p 'test_*.py' -v \
  2>&1 | tee "$ROOT/metadata/python-tests.log"

echo "[2/4] Reference demonstration"
python3 "$ROOT/code/run_reference.py" \
  | tee "$ROOT/metadata/reference-output.json"

echo "[3/4] LaTeX build"
cd "$ROOT/paper"
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  pcfm_ipra_framework.tex \
  2>&1 | tee "$ROOT/metadata/latex-build.log"

echo "[4/4] PDF metadata"
pdfinfo pcfm_ipra_framework.pdf \
  | tee "$ROOT/metadata/pdfinfo.txt"

echo "Build completed."
