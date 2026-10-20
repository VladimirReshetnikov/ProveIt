#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error formalism218_appendix.tex
pdflatex -interaction=nonstopmode -halt-on-error formalism218_appendix.tex
