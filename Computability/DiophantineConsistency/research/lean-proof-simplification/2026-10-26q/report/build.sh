#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
pdflatex -halt-on-error -interaction=nonstopmode new-proof-simplifications.tex
pdflatex -halt-on-error -interaction=nonstopmode new-proof-simplifications.tex
