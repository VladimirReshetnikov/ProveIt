#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
command -v python3 >/dev/null || { echo "python3 is required" >&2; exit 1; }
command -v pdflatex >/dev/null || { echo "pdflatex is required" >&2; exit 1; }
python3 code/verify_finite.py --output data/finite_checks.json
for pass in 1 2 3; do
  pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error article.tex
done
printf '\nBuilt article.pdf. Checksums supplied with the original package are not regenerated.\n'
