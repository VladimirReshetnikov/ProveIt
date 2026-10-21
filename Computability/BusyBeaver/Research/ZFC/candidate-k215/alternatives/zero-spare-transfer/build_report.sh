#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Requires an existing TeX installation with the standard packages named in report.tex.
# This script installs nothing and does not use shell escape.
out="${1:-/tmp/zero-spare-report-build}"
mkdir -p "$out"
for pass in 1 2; do
  pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory "$out" report.tex
done
printf 'Rebuilt PDF: %s/report.pdf\n' "$out"
