#!/bin/sh
# Rebuild this standalone article and its finite regression record.
# Overwrites only generated files in this package directory.
set -eu
cd "$(dirname "$0")"
command -v latexmk >/dev/null 2>&1 || {
    echo 'latexmk is required. Install a TeX distribution with the source packages.' >&2
    exit 1
}
command -v python3 >/dev/null 2>&1 || {
    echo 'Python 3.10 or later is required for the finite verifier.' >&2
    exit 1
}
mkdir -p data
python3 code/verify_finite.py --order 12 --output data/verification.json \
    > data/verification_console.txt
latexmk -pdf -interaction=nonstopmode -halt-on-error finite_symmetry_descent.tex
printf '\nBuilt finite_symmetry_descent.pdf and reran the finite checks.\n'
