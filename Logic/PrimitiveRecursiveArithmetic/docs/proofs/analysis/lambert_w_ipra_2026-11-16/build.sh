#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"
python3 scripts/verify_lambert_w.py \
  --report evidence/verification_report.txt \
  --json evidence/verification_report.json
latexmk -pdf -interaction=nonstopmode -halt-on-error lambert_w_ipra.tex
printf 'Build and verification completed.\n'
