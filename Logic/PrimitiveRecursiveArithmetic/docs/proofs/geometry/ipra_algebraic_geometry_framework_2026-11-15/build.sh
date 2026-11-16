#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

mkdir -p verification metadata
rm -rf code/__pycache__

python3 -m unittest discover -s code -v 2>&1 | tee verification/python_tests.txt
python3 code/zariski_descent.py | tee verification/demo_output.json > metadata/validation.json

(
  cd paper
  latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_algebraic_geometry_framework.tex
)

if command -v pdfinfo >/dev/null 2>&1; then
  pdfinfo paper/ipra_algebraic_geometry_framework.pdf > verification/pdfinfo.txt
fi
if command -v pdftotext >/dev/null 2>&1; then
  pdftotext paper/ipra_algebraic_geometry_framework.pdf verification/pdf_text.txt
fi
if command -v pdffonts >/dev/null 2>&1; then
  pdffonts paper/ipra_algebraic_geometry_framework.pdf > verification/pdffonts.txt
fi

{
  echo "LaTeX diagnostic audit"
  if grep -E "LaTeX Warning:.*(undefined|Citation)|There were undefined references|Overfull \\hbox|^!" paper/ipra_algebraic_geometry_framework.log; then
    echo "Diagnostic patterns found above."
    exit 1
  else
    echo "No undefined references/citations, overfull boxes, or TeX errors found."
  fi
} > verification/latex_audit.txt

(
  cd paper
  latexmk -c ipra_algebraic_geometry_framework.tex >/dev/null
)
rm -rf code/__pycache__

find . -type f \
  ! -name 'MANIFEST.sha256' \
  ! -path './paper/*.aux' \
  ! -path './paper/*.fdb_latexmk' \
  ! -path './paper/*.fls' \
  ! -path './paper/*.log' \
  ! -path './paper/*.out' \
  ! -path './paper/*.toc' \
  ! -path './code/__pycache__/*' \
  -print0 | sort -z | xargs -0 sha256sum > MANIFEST.sha256

echo "Build complete: paper/ipra_algebraic_geometry_framework.pdf"
