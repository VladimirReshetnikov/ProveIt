#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
PYTHON_BIN="${PYTHON_BIN:-python3}"
command -v "$PYTHON_BIN" >/dev/null
command -v pdflatex >/dev/null
"$PYTHON_BIN" verify.py --output verification.json --export-dir example
"$PYTHON_BIN" verify_compact.py
"$PYTHON_BIN" verify_spatial.py
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex > "build-pass${pass}.log"
done
if grep -Eq 'undefined references|Citation .* undefined|Reference .* undefined' article.log; then
  echo 'Unresolved LaTeX references remain.' >&2
  exit 1
fi
printf '\nBuilt article.pdf and regenerated all three verification receipts.\n'
