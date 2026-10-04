#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
mkdir -p build
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build definable_surreals.tex
else
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build definable_surreals.tex
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build definable_surreals.tex
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build definable_surreals.tex
fi
cp build/definable_surreals.pdf definable_surreals.pdf

