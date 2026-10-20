#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 -B make_table.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
