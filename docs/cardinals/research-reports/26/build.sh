#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'Error: pdflatex is required. Install TeX Live or an equivalent distribution.' >&2
    exit 1
fi
for pass in 1 2 3; do
    printf '\nBuild pass %s/3\n' "$pass"
    pdflatex -interaction=nonstopmode -halt-on-error Ultraexacting_Prikry_Cores.tex
done
