#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 make_tables.py
pdflatex -interaction=nonstopmode -halt-on-error Sparse_Cut_Grammars.tex
pdflatex -interaction=nonstopmode -halt-on-error Sparse_Cut_Grammars.tex
pdflatex -interaction=nonstopmode -halt-on-error Sparse_Cut_Grammars.tex
