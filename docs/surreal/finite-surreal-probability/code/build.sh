#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
mkdir -p _build
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error \
        -outdir=_build surreal_probability.tex
else
    for pass in 1 2 3; do
        pdflatex -interaction=nonstopmode -halt-on-error \
            -output-directory=_build surreal_probability.tex
    done
fi
cp _build/surreal_probability.pdf surreal_probability.pdf
printf '%s\n' 'Built surreal_probability.pdf. Inspect _build/surreal_probability.log for warnings.'
