#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
export PYTHONPATH="$ROOT/reference${PYTHONPATH:+:$PYTHONPATH}"
python3 -m unittest -v "$ROOT/reference/test_strive_reference.py" \
  |& tee "$ROOT/validation/python_tests.txt"
python3 "$ROOT/reference/generate_examples.py"
(
  cd "$ROOT/paper"
  latexmk -pdf -interaction=nonstopmode -halt-on-error strive_ipra_framework.tex \
    |& tee "$ROOT/validation/latex_build.txt"
)
