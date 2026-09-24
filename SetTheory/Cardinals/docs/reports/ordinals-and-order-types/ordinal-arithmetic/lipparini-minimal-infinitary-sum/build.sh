#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
pdflatex -interaction=nonstopmode -halt-on-error explicit_ordinal_sum.tex
pdflatex -interaction=nonstopmode -halt-on-error explicit_ordinal_sum.tex
pdflatex -interaction=nonstopmode -halt-on-error explicit_ordinal_sum.tex
