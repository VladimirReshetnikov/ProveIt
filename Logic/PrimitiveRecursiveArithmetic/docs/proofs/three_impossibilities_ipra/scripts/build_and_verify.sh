#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
mkdir -p build evidence
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=build three_classical_impossibilities_ipra.tex
cp build/three_classical_impossibilities_ipra.pdf .
python3 scripts/finite_checks.py | tee evidence/finite_checks.txt
python /home/oai/skills/pdfs/scripts/pdf_preflight.py \
  three_classical_impossibilities_ipra.pdf
