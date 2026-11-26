#!/usr/bin/env bash
set -euo pipefail
report_dir="$(cd "$(dirname "$0")/.." && pwd)"
cd "$report_dir"
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
