#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error shared_witness_bundles.tex
pdflatex -interaction=nonstopmode -halt-on-error shared_witness_bundles.tex
