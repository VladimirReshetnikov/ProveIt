#!/usr/bin/env bash
# Rebuild the report with an installed TeX Live or compatible pdfLaTeX.
# No downloads, dependency installation, Lean compilation or source mutation.
set -euo pipefail
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
