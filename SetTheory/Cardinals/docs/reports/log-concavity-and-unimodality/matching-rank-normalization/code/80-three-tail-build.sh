#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
pdflatex -interaction=nonstopmode -halt-on-error sharp-weighted-rank-boundary.tex
pdflatex -interaction=nonstopmode -halt-on-error sharp-weighted-rank-boundary.tex
