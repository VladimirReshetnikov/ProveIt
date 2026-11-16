#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"
python3 -m unittest -v reference/test_pfig_reference.py |& tee validation/python_tests.txt
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_pfig_framework.tex |& tee ../validation/latex_build.txt
