#!/bin/sh
# Rebuild the report using a normal TeX installation.
set -eu

report_dir=$(CDPATH= cd "$(dirname "$0")" && pwd)
cd "$report_dir"

for report_pass in 1 2 3
do
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error dimension_invariance.tex
done
