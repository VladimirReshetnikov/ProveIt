#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

mkdir -p verification
(cd code && python3 -m unittest -v test_finite_use_kernel.py) \
  > verification/python_tests.txt 2>&1
python3 code/finite_use_kernel.py > verification/demo_output.json

PDF_HELPER="${PDF_HELPER:-/home/oai/skills/pdfs/scripts/latex_to_pdf.py}"
if [[ -f "$PDF_HELPER" ]]; then
  python3 "$PDF_HELPER" \
    --engine pdflatex --clean \
    -o "$ROOT/ipra_finite_use_framework.pdf" \
    "$ROOT/ipra_finite_use_framework.tex"
elif command -v latexmk >/dev/null 2>&1; then
  BUILD_DIR="$ROOT/.tex-build"
  rm -rf "$BUILD_DIR"
  mkdir -p "$BUILD_DIR"
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    -outdir="$BUILD_DIR" "$ROOT/ipra_finite_use_framework.tex"
  cp "$BUILD_DIR/ipra_finite_use_framework.pdf" \
    "$ROOT/ipra_finite_use_framework.pdf"
  rm -rf "$BUILD_DIR"
elif command -v pdflatex >/dev/null 2>&1; then
  for _ in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory="$ROOT" "$ROOT/ipra_finite_use_framework.tex" >/dev/null
  done
  rm -f "$ROOT"/*.aux "$ROOT"/*.log "$ROOT"/*.out "$ROOT"/*.toc
else
  echo "No usable LaTeX engine found." >&2
  exit 1
fi

# The helper may leave diagnostic directories in the source directory.
rm -rf "$ROOT"/latex_build_* "$ROOT"/code/__pycache__

find . -type f \
  ! -name 'MANIFEST.sha256' \
  ! -path './verification/rendered/*' \
  ! -path './verification/montage/*' \
  -print0 | sort -z | xargs -0 sha256sum > MANIFEST.sha256
