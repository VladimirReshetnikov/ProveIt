#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
command -v pdflatex >/dev/null || { echo 'pdflatex is required.' >&2; exit 1; }
mkdir -p build
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build \
    Cardinals5_Prikry_Finite_Choice.tex > "build/pass-${pass}.txt" 2>&1 || {
      cat "build/pass-${pass}.txt" >&2
      exit 1
    }
done
cp build/Cardinals5_Prikry_Finite_Choice.pdf .
echo 'Built Cardinals5_Prikry_Finite_Choice.pdf'
