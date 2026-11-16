#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$ROOT/verification"

echo "[1/4] exact Python tests"
(
  cd "$ROOT/code"
  python3 -m unittest -v test_certificate_kernel.py
) 2>&1 | tee "$ROOT/verification/python_tests.txt"

echo "[2/4] example certificate"
PYTHONPATH="$ROOT/code" \
  python3 "$ROOT/code/certificate_kernel.py" \
  "$ROOT/examples/framework_certificate.json" \
  | tee "$ROOT/verification/certificate_run.json"

echo "[3/4] PDF build"
(
  cd "$ROOT/paper"
  latexmk -pdf -interaction=nonstopmode -halt-on-error cfp_contract_compiler.tex
) 2>&1 | tee "$ROOT/verification/latex_build.txt"

echo "[4/4] PDF text/preflight"
pdfinfo "$ROOT/paper/cfp_contract_compiler.pdf" \
  | tee "$ROOT/verification/pdfinfo.txt"
pdftotext "$ROOT/paper/cfp_contract_compiler.pdf" \
  "$ROOT/verification/cfp_contract_compiler.txt"
if grep -nE '\?\?|LaTeX Warning:.*undefined|Missing character' \
    "$ROOT/verification/cfp_contract_compiler.txt"; then
  echo "unexpected unresolved marker in PDF text" >&2
  exit 1
fi

echo "Build complete."
