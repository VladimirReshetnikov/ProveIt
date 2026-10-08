#!/bin/sh
set -eu
cd "$(dirname "$0")"
# Three passes also stabilize the two-page contents after a clean build.
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
