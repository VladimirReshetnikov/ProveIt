#!/bin/sh
# Build from any working directory. Requires pdfLaTeX and the TeX packages
# listed in stern_conjecture_note.tex. No network access is performed.
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error stern_conjecture_note.tex
pdflatex -interaction=nonstopmode -halt-on-error stern_conjecture_note.tex
