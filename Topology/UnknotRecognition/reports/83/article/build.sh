#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error four_copy_patterns.tex
pdflatex -interaction=nonstopmode -halt-on-error four_copy_patterns.tex
pdflatex -interaction=nonstopmode -halt-on-error four_copy_patterns.tex
