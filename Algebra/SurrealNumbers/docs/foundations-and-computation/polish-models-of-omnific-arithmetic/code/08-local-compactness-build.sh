#!/usr/bin/env sh
# Rebuild the mathematical manuscript and rerun exact finite checks.
set -eu
cd -- "$(dirname -- "$0")"
command -v latexmk >/dev/null 2>&1 || {
    echo "Error: latexmk was not found. Install a suitable TeX Live distribution." >&2
    exit 1
}
command -v python3 >/dev/null 2>&1 || {
    echo "Error: python3 was not found. Python 3.10 or later is required." >&2
    exit 1
}
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
python3 verify.py --output verification_results.json
