#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error fermat_two_squares_ipra.tex
pdflatex -interaction=nonstopmode -halt-on-error fermat_two_squares_ipra.tex
