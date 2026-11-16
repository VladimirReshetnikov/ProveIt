#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

PYTHONPATH=reference python3 -m unittest -v reference/test_fiber_reference.py
PYTHONPATH=reference python3 reference/generate_examples.py

cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error fiber_ipra_framework.tex
