#!/usr/bin/env bash
# Rebuild the self-contained article and run the exact finite regression suite.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
for tool in python3 pdflatex; do
  command -v "$tool" >/dev/null 2>&1 || {
    printf 'Required executable not found: %s\n' "$tool" >&2
    exit 1
  }
done
mkdir -p build data
python3 code/verify.py --output data/verification.json
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error \
       -output-directory=build article.tex > "build/latex-pass-${pass}.txt" 2>&1; then
    tail -80 "build/latex-pass-${pass}.txt" >&2
    exit 1
  fi
done
if grep -Eq 'There were undefined references|There were undefined citations|Label\(s\) may have changed' build/article.log; then
  printf 'Unresolved LaTeX references: inspect build/article.log.\n' >&2
  exit 1
fi
cp -- build/article.pdf article.pdf
printf '\nCreated article.pdf. Exact check results: data/verification.json\n'
