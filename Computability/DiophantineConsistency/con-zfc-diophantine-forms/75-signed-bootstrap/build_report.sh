#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 check_displayed_system.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
