#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 code/verify.py --output verification.json
python3 code/compile_interval.py --output compiler_report.json
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
