#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$ROOT/verification"
python3 "$ROOT/code/test_cbip_kernel.py" 2>&1 | tee "$ROOT/verification/test_output.txt"
(
  cd "$ROOT/paper"
  latexmk -pdf -interaction=nonstopmode -halt-on-error cbip_framework.tex
)
