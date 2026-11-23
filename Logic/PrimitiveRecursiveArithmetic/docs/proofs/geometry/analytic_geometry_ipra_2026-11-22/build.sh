#!/usr/bin/env bash
set -euo pipefail
packet_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd -- "$packet_dir"
python3 code/build_inventory.py
mkdir -p artifacts
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex > artifacts/latex-build.log 2>&1
echo 'Built report.pdf'
