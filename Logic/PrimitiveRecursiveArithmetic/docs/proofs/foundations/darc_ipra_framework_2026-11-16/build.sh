#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$ROOT/validation" "$ROOT/examples"
PYTHONPATH="$ROOT/reference" python3 -m unittest -v reference.test_darc_reference \
  2>&1 | tee "$ROOT/validation/test_output.txt"
PYTHONPATH="$ROOT/reference" python3 "$ROOT/reference/generate_demo.py" \
  > "$ROOT/examples/demo.json"
PYTHONPATH="$ROOT/reference" python3 "$ROOT/reference/validate_artifact.py" \
  2>&1 | tee "$ROOT/validation/artifact_validation.txt"
(
  cd "$ROOT/paper"
  latexmk -pdf -interaction=nonstopmode -halt-on-error darc_ipra_framework.tex \
    > "$ROOT/validation/latex_build.log" 2>&1
)
pdfinfo "$ROOT/paper/darc_ipra_framework.pdf" > "$ROOT/validation/pdfinfo.txt"
pdftotext "$ROOT/paper/darc_ipra_framework.pdf" "$ROOT/validation/pdftotext.txt"
echo "Build completed successfully." | tee "$ROOT/validation/build_summary.txt"
