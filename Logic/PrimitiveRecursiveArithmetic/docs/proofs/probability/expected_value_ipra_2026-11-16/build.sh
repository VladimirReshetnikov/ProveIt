#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
python3 "$ROOT/code/validate_expected_value.py" --output "$ROOT/validation/validation.json"
cd "$ROOT/paper"
latexmk -pdf -interaction=nonstopmode -halt-on-error expected_value_ipra.tex
