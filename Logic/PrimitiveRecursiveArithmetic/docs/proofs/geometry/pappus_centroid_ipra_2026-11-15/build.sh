#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 code/pappus_checker.py certificates/sample_certificate.json | tee verification_output.txt
latexmk -pdf -interaction=nonstopmode -halt-on-error pappus_centroid_ipra.tex
find . -type f \
  ! -path './build/*' ! -path '*/__pycache__/*' ! -name '*.pyc' \
  ! -name 'SHA256SUMS' \
  ! -name '*.aux' ! -name '*.fdb_latexmk' ! -name '*.fls' \
  ! -name '*.log' ! -name '*.out' ! -name '*.toc' \
  -print0 | sort -z | xargs -0 sha256sum > SHA256SUMS
printf 'Build complete.\n'
