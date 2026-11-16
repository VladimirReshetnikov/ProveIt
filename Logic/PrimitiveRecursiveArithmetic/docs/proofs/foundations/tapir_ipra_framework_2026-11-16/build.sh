#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"
mkdir -p validation examples

{
  echo "TAPIR reference tests"
  echo "UTC: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  PYTHONPATH=reference python3 -m unittest -v reference/test_tapir_reference.py
} 2>&1 | tee validation/TESTS.txt

PYTHONPATH=reference python3 reference/generate_demo.py | tee validation/DEMO_GENERATION.txt

{
  echo "Lean executable: $(command -v lean || echo unavailable)"
  echo "Lake executable: $(command -v lake || echo unavailable)"
  echo
  echo "Placeholder scan:"
  grep -RIn --include='*.lean' -E '\bsorry\b|\badmit\b' lean/TAPIR || true
  echo
  echo "No-placeholder candidates:"
  for f in lean/TAPIR/Kernel.lean lean/TAPIR/Schedule.lean; do
    if grep -Eq '\bsorry\b|\badmit\b' "$f"; then
      echo "FAIL $f contains a placeholder"
      exit 1
    else
      echo "PASS $f"
    fi
  done
} > validation/STATIC_SCAN.txt

(
  cd paper
  latexmk -pdf -interaction=nonstopmode -halt-on-error tapir_ipra_framework.tex
)

pdfinfo paper/tapir_ipra_framework.pdf > validation/PDF_INFO.txt
pdffonts paper/tapir_ipra_framework.pdf > validation/FONT_INFO.txt
python /home/oai/skills/pdfs/scripts/pdf_preflight.py \
  paper/tapir_ipra_framework.pdf > validation/PDF_PREFLIGHT.txt 2>&1 || true

find . -type f \
  ! -path './paper/*.aux' \
  ! -path './paper/*.fdb_latexmk' \
  ! -path './paper/*.fls' \
  ! -path './paper/*.log' \
  ! -path './paper/*.out' \
  ! -path './paper/*.toc' \
  ! -name 'manifest.txt' \
  | sed 's#^./##' | sort > manifest.txt

echo "Build complete: paper/tapir_ipra_framework.pdf"
