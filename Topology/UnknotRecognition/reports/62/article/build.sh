#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error sparse_incidence.tex
pdflatex -interaction=nonstopmode -halt-on-error sparse_incidence.tex
pdflatex -interaction=nonstopmode -halt-on-error sparse_incidence.tex
