#!/usr/bin/env bash
# Build from the directory containing this script. Python 3.10+ and TeX Live required.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v python3 >/dev/null || { echo 'python3 is required.' >&2; exit 1; }
command -v latexmk >/dev/null || { echo 'latexmk and a standard TeX Live installation are required.' >&2; exit 1; }
python3 verification.py
mkdir -p .build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=.build article.tex
cp .build/article.pdf article.pdf
printf '\nBuilt article.pdf. Checks are recorded in verification.json.\n'
