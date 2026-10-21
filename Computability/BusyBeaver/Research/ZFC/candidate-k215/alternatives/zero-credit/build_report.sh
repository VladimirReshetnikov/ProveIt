#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
report_build=$(mktemp -d)
trap 'rm -rf "$report_build"' EXIT
pdflatex -interaction=nonstopmode -halt-on-error -output-directory "$report_build" ZC215.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory "$report_build" ZC215.tex
cp "$report_build/ZC215.pdf" ZC215.pdf
printf '%s\n' 'Built ZC215.pdf. A rebuilt PDF may have a different timestamp/hash than the released manifest.'
