#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
if ! command -v latexmk >/dev/null 2>&1; then
    printf '%s\n' 'Error: latexmk is required. Install a TeX distribution including newtx.' >&2
    exit 1
fi
if ! command -v python3 >/dev/null 2>&1; then
    printf '%s\n' 'Error: Python 3.10 or later is required for the finite checks.' >&2
    exit 1
fi
latexmk -pdf -interaction=nonstopmode -halt-on-error critical_point_defects.tex
python3 code/finite_regression.py
printf '%s\n' 'Built critical_point_defects.pdf and reran finite algebraic checks.'
