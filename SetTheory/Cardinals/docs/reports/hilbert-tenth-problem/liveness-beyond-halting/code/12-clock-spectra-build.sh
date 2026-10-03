#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v python3 >/dev/null 2>&1 || { echo 'python3 is required' >&2; exit 1; }
command -v pdflatex >/dev/null 2>&1 || { echo 'pdflatex is required' >&2; exit 1; }
python3 code/test_all.py
python3 code/verify_export.py examples/quadratic_certificate.json
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
