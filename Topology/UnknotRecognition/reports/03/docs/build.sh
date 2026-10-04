#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error implementation_report.tex
pdflatex -interaction=nonstopmode -halt-on-error implementation_report.tex
