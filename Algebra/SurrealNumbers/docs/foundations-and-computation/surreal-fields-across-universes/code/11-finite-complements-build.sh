#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
command -v python3 >/dev/null || { echo 'Python 3 is required.' >&2; exit 1; }
command -v latexmk >/dev/null || { echo 'latexmk and a TeX distribution are required.' >&2; exit 1; }
python3 checks/finite_checks.py
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error article.tex
printf '\nBuilt %s/article.pdf\n' "$PWD"
