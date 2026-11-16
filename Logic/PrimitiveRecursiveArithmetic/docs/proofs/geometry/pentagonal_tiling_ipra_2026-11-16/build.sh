#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"
mkdir -p verification
python3 code/verify_pentagonal_tilings.py | tee verification/run_stdout.json
latexmk -pdf -interaction=nonstopmode -halt-on-error pentagonal_tiling_ipra.tex \
  > verification/latexmk_stdout.txt 2>&1
pdfinfo pentagonal_tiling_ipra.pdf > verification/pdfinfo.txt
pdftotext pentagonal_tiling_ipra.pdf verification/pentagonal_tiling_ipra.txt
printf 'Build completed.\n'
