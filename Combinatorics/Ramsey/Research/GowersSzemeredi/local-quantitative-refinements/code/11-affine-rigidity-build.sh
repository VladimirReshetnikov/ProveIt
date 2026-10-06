#!/usr/bin/env bash
# Run from any directory. Requires Python 3 and pdfLaTeX on PATH.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
for cmd in python3 pdflatex; do
  command -v "$cmd" >/dev/null 2>&1 || {
    printf 'Required command not found: %s\n' "$cmd" >&2
    exit 1
  }
done
mkdir -p checks
python3 checks/verify.py --output checks/verification_results.json \
  | tee checks/verification_log.txt
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
printf '\nBuilt article.pdf and refreshed the exact verification results.\n'
