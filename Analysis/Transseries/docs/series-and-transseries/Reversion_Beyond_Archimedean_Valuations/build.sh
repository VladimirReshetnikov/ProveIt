#!/bin/sh
set -eu
cd "$(dirname "$0")"
command -v python3 >/dev/null 2>&1 || { echo "python3 is required" >&2; exit 1; }
command -v pdflatex >/dev/null 2>&1 || { echo "pdflatex is required" >&2; exit 1; }
python3 verify.py
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
