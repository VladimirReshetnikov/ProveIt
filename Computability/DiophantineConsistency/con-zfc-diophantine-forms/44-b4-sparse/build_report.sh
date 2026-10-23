#!/bin/sh
# A standard complete TeX Live installation needs only pdflatex twice.
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
