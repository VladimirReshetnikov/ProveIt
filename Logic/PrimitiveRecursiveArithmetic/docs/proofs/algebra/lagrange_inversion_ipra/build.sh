#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT/paper"
latexmk -pdf -interaction=nonstopmode -halt-on-error lagrange_inversion_ipra.tex
cd "$ROOT"
python3 code/verify.py
