#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error component_gauge_atlases.tex
pdflatex -interaction=nonstopmode -halt-on-error component_gauge_atlases.tex
pdflatex -interaction=nonstopmode -halt-on-error component_gauge_atlases.tex
