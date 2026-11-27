#!/usr/bin/env bash
set -euo pipefail
archive_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$archive_root"
for paper in prime_product_limits symplectic_precision; do
  pdflatex -interaction=nonstopmode -halt-on-error "$paper.tex"
  pdflatex -interaction=nonstopmode -halt-on-error "$paper.tex"
done
