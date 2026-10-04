#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error hat_inspection_frontier.tex
pdflatex -interaction=nonstopmode -halt-on-error hat_inspection_frontier.tex
pdflatex -interaction=nonstopmode -halt-on-error hat_inspection_frontier.tex
