#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
for tool in python3 latexmk; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'Required program not found: %s\n' "$tool" >&2
    exit 1
  fi
done
python3 code/finite_checks.py --output data/finite_checks.json
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  surreal_lexicographic_boundaries.tex
