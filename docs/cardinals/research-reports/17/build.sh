#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdflatex is not on PATH. Install a LaTeX distribution first.' >&2
    exit 1
fi
for pass in 1 2 3; do
    printf '\nLaTeX pass %s of 3\n' "$pass"
    pdflatex -interaction=nonstopmode -halt-on-error Thin_Sections_and_Saturation.tex
done
printf '\nBuilt Thin_Sections_and_Saturation.pdf\n'
