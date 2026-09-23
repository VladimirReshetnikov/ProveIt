#!/bin/sh
# Reproduce the finite tests and compile the standalone article.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
for program in python3 pdflatex; do
    if ! command -v "$program" >/dev/null 2>&1; then
        printf 'Required program not found: %s\n' "$program" >&2
        exit 1
    fi
done
python3 -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else "Python 3.10 or later is required.")'
python3 verify.py --output verification_report.json
for pass in 1 2 3; do
    printf '\nLaTeX pass %s of 3\n' "$pass"
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
        omnific_normalization.tex
done
printf '\nBuilt: omnific_normalization.pdf\n'
printf 'Finite checks passed; this is not a formal proof certificate.\n'
