#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
command -v python3 >/dev/null 2>&1 || { echo 'python3 is required.' >&2; exit 1; }
command -v latexmk >/dev/null 2>&1 || { echo 'latexmk is required.' >&2; exit 1; }
python3 code/finite_checks.py --output data/finite_checks.json
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
