#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"
python3 code/gaussian_certificates.py \
  --output evidence/validation.json \
  --summary evidence/validation.txt
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error normal_distribution_ipra.tex
