#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$ROOT/validation"

(
  cd "$ROOT/code"
  python -m unittest -v test_pcog.py 2>&1
) | tee "$ROOT/validation/python_tests.txt"

python "$ROOT/code/generate_example.py" \
  > "$ROOT/validation/example_generation.txt" 2>&1

python -m py_compile \
  "$ROOT/code/pcog.py" \
  "$ROOT/code/test_pcog.py" \
  "$ROOT/code/generate_example.py"

(
  cd "$ROOT/paper"
  latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_pcog_framework.tex
) > "$ROOT/validation/latex_build.txt" 2>&1

pdfinfo "$ROOT/paper/ipra_pcog_framework.pdf" \
  > "$ROOT/validation/pdfinfo.txt"

echo "Build completed successfully."
