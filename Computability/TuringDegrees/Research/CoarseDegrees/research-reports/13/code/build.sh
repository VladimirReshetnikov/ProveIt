#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 checks/finite_checks.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
