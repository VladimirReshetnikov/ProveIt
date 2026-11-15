#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
cd "$root/paper"
latexmk -pdf -interaction=nonstopmode -halt-on-error bohr_mollerup_ipra.tex
cd "$root/code"
python3 test_bm_bounds.py
python3 bm_bounds.py --verify "$root/sample_certificate_half.json"
