#!/bin/sh
set -eu
cd "$(dirname "$0")/report"
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
