#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
pdflatex -interaction=nonstopmode -halt-on-error two-element-matroid-lorentzian.tex
pdflatex -interaction=nonstopmode -halt-on-error two-element-matroid-lorentzian.tex
