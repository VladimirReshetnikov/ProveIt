#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error Marginal_Critical_Transseries.tex
done
