#!/bin/sh
# Requires an ordinary, complete TeX installation with article, amsmath,
# amssymb, geometry, lmodern, hyperref, and microtype.
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error standalone.tex
pdflatex -interaction=nonstopmode -halt-on-error standalone.tex
