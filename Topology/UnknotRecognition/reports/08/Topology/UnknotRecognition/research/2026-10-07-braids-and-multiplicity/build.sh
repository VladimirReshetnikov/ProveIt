#!/usr/bin/env sh
# Rebuild the standalone article with resolved contents and cross-references.
set -eu
cd "$(dirname "$0")"
for pass in 1 2 3
do
    pdflatex -interaction=nonstopmode -halt-on-error unknot_recognition_progress.tex
done
