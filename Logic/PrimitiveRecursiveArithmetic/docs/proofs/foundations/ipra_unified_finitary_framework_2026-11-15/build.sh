#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"

printf '== Exact Python checks ==\n'
(
  cd "$ROOT/code"
  python3 -m unittest -v test_reference_framework.py
  python3 reference_framework.py > "$ROOT/validation/reference_results.json"
)

printf '\n== LaTeX report ==\n'
(
  cd "$ROOT/paper"
  latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_unified_framework.tex
)

printf '\nBuild complete: %s\n' "$ROOT/paper/ipra_unified_framework.pdf"
