#!/bin/sh
# Build the report with local TeX packages; do not download dependencies.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
base='Normal_Measures_and_Prikry_Layers'
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'Error: pdflatex is not installed or is not on PATH.' >&2
    exit 1
fi
work=$(mktemp -d "${TMPDIR:-/tmp}/cardinals4-tex.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error \
        -outdir="$work" "$base.tex"
else
    for pass in 1 2 3; do
        pdflatex -interaction=nonstopmode -halt-on-error \
            -output-directory="$work" "$base.tex"
    done
fi
if [ ! -s "$work/$base.pdf" ]; then
    printf '%s\n' 'Error: TeX did not create the expected PDF.' >&2
    exit 1
fi
cp "$work/$base.pdf" "$base.pdf"
printf '\nBuilt %s\n' "$base.pdf"
