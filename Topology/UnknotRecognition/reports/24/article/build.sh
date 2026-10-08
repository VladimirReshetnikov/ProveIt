#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error unknot_compression_kernels.tex
bibtex unknot_compression_kernels
pdflatex -interaction=nonstopmode -halt-on-error unknot_compression_kernels.tex
pdflatex -interaction=nonstopmode -halt-on-error unknot_compression_kernels.tex
