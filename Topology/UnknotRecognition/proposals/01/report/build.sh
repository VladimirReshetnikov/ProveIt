#!/bin/sh
# Build the self-contained article; run from any directory.
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error unknot_speedup.tex
pdflatex -interaction=nonstopmode -halt-on-error unknot_speedup.tex
pdflatex -interaction=nonstopmode -halt-on-error unknot_speedup.tex
