#!/bin/sh
# Compile locally; no shell escape or network access is used.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v latexmk >/dev/null 2>&1; then
    echo 'Error: latexmk is required. Install it with a LaTeX distribution.' >&2
    exit 1
fi
mkdir -p build
latexmk -pdf -halt-on-error -interaction=nonstopmode -outdir=build paper.tex
cp build/paper.pdf paper.pdf
printf '%s\n' 'Built paper.pdf'
