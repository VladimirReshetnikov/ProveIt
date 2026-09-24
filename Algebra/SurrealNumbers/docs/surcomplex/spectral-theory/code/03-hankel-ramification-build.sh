#!/bin/sh
set -eu
cd "$(dirname "$0")"
for pass in 1 2 3; do
    pdflatex -halt-on-error -interaction=nonstopmode article.tex
done
