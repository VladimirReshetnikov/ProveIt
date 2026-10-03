#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
command -v latexmk >/dev/null || { echo "latexmk is required." >&2; exit 1; }
command -v python >/dev/null || { echo "Python 3.10+ is required." >&2; exit 1; }
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
python verify.py | tee verification.txt
