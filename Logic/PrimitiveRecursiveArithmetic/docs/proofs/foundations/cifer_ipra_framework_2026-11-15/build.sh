#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"

cd "$ROOT/code"
python3 -m unittest -v test_cifer.py 2>&1 | tee "$ROOT/validation/python_tests.txt"
python3 demo.py > "$ROOT/validation/demo_stdout.json"

cd "$ROOT/paper"
latexmk -pdf -interaction=nonstopmode -halt-on-error cifer_ipra_framework.tex \
  > "$ROOT/validation/latex_build.txt" 2>&1
pdfinfo cifer_ipra_framework.pdf > "$ROOT/validation/pdfinfo.txt"
if [[ -f /home/oai/skills/pdfs/scripts/pdf_preflight.py ]]; then
  python /home/oai/skills/pdfs/scripts/pdf_preflight.py cifer_ipra_framework.pdf \
    > "$ROOT/validation/pdf_preflight.txt" 2>&1 || true
else
  echo "PDF preflight helper not available; pdfinfo completed." \
    > "$ROOT/validation/pdf_preflight.txt"
fi

cd "$ROOT"
find . -type f \
  ! -path './renders/*' \
  ! -name 'MANIFEST.sha256' \
  ! -name '*.aux' ! -name '*.fdb_latexmk' ! -name '*.fls' \
  ! -name '*.log' ! -name '*.out' ! -name '*.toc' \
  -print0 | sort -z | xargs -0 sha256sum > MANIFEST.sha256

echo "Build and validation complete."
