#!/usr/bin/env bash
set -euo pipefail

package_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd -- "$package_dir"
article_stem="polylogarithm_resonance_and_inverse_transseries"
mkdir -p build/latex
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    -outdir=build/latex "$article_stem.tex"
else
  for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory=build/latex "$article_stem.tex"
  done
fi
cp -- "build/latex/$article_stem.pdf" "$article_stem.pdf"
