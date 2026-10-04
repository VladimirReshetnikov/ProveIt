#!/bin/sh
# Run from any directory. A working pdflatex installation is required.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "pdflatex was not found. Install a LaTeX distribution first." >&2
    exit 1
fi
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error polish_presburger_glazer.tex
done
printf '\nBuilt: %s/polish_presburger_glazer.pdf\n' "$PWD"
