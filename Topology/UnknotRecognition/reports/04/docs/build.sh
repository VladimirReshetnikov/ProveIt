#!/bin/sh
# Run from any directory; requires a LaTeX distribution with the listed packages.
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
