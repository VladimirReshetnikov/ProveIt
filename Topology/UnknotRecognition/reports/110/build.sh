#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
pdflatex -interaction=nonstopmode -halt-on-error ordered_pivot_interfaces.tex
pdflatex -interaction=nonstopmode -halt-on-error ordered_pivot_interfaces.tex
pdflatex -interaction=nonstopmode -halt-on-error ordered_pivot_interfaces.tex
