#!/bin/sh
set -eu
cd "$(dirname "$0")"
# ProveIt edit (2026-09-29): the verification rerun writes into build/
# (ignored by git) instead of overwriting the recorded
# verification_results.json, and PYTHON may name the interpreter
# (python3 by default; use PYTHON=py on Windows).
PYTHON=${PYTHON:-python3}
command -v "$PYTHON" >/dev/null 2>&1 || { echo "$PYTHON is required (set PYTHON)" >&2; exit 1; }
command -v pdflatex >/dev/null 2>&1 || { echo "pdflatex is required" >&2; exit 1; }
mkdir -p build
"$PYTHON" verify.py --output build/verification_results.json
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
