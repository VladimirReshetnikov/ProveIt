#!/bin/sh
set -eu
cd "$(dirname "$0")/report"
pdflatex -interaction=nonstopmode -halt-on-error pa194nq.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194nq.tex
