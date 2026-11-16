#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$ROOT/verification"

python "$ROOT/code/generate_examples.py" \
  >"$ROOT/verification/example_generation.txt" 2>&1
PYTHONPATH="$ROOT/code" python "$ROOT/code/test_finitary_kernel.py" \
  >"$ROOT/verification/python_tests.txt" 2>&1

cd "$ROOT/paper"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    ipra_finitary_interface_compiler.tex \
    >"$ROOT/verification/latex_build.txt" 2>&1
elif command -v pdflatex >/dev/null 2>&1; then
  : >"$ROOT/verification/latex_build.txt"
  pdflatex -interaction=nonstopmode -halt-on-error \
    ipra_finitary_interface_compiler.tex \
    >>"$ROOT/verification/latex_build.txt" 2>&1
  pdflatex -interaction=nonstopmode -halt-on-error \
    ipra_finitary_interface_compiler.tex \
    >>"$ROOT/verification/latex_build.txt" 2>&1
else
  echo "No LaTeX engine found" >"$ROOT/verification/latex_build.txt"
  exit 1
fi
