#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
printf '%s\n' 'Built report.pdf. Render and visually inspect any modified report before redistribution.'
