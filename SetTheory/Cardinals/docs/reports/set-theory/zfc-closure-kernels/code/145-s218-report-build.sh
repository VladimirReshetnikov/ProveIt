#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B make_tables.py
pdflatex -halt-on-error -interaction=nonstopmode report.tex
pdflatex -halt-on-error -interaction=nonstopmode report.tex
pdflatex -halt-on-error -interaction=nonstopmode report.tex
