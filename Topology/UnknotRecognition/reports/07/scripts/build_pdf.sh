#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root/paper"
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
  -outdir=build unknot_structural_compression.tex
cp build/unknot_structural_compression.pdf unknot_structural_compression.pdf
