#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
pdflatex -interaction=nonstopmode -halt-on-error all-two-by-three-cores.tex
pdflatex -interaction=nonstopmode -halt-on-error all-two-by-three-cores.tex
