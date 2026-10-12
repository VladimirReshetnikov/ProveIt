#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
pdflatex -interaction=nonstopmode -halt-on-error cographic_persistence.tex
pdflatex -interaction=nonstopmode -halt-on-error cographic_persistence.tex
pdflatex -interaction=nonstopmode -halt-on-error cographic_persistence.tex
