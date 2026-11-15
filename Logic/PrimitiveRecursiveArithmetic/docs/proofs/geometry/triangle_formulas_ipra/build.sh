#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mkdir -p verification
python3 python/verify.py > verification/numerical_checks.txt
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error \
  triangle_formulas_ipra.tex > verification/latex_final_1.log 2>&1
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error \
  triangle_formulas_ipra.tex > verification/latex_final_2.log 2>&1
python3 -c 'from pathlib import Path; p=Path("triangle_formulas_ipra.pdf"); print(f"Built {p.name}: {p.stat().st_size} bytes")'
