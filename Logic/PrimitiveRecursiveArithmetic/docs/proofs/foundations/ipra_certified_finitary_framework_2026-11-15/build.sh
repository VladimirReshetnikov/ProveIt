#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"

mkdir -p "$ROOT/validation"
(
  cd "$ROOT/code"
  python -m unittest -v test_reference_framework.py
) 2>&1 | tee "$ROOT/validation/python_tests.txt"

(
  cd "$ROOT/paper"
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    ipra_certified_finitary_framework.tex
) 2>&1 | tee "$ROOT/validation/latex_build.txt"

pdfinfo "$ROOT/paper/ipra_certified_finitary_framework.pdf" \
  > "$ROOT/validation/pdfinfo.txt"

printf 'Build completed successfully.\n'
