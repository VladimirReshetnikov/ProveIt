#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
command -v python3 >/dev/null || { echo 'Python 3 is required.' >&2; exit 1; }
command -v latexmk >/dev/null || { echo 'latexmk and a LaTeX distribution are required.' >&2; exit 1; }
python3 code/finite_checks.py --output data/finite_checks.json
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
