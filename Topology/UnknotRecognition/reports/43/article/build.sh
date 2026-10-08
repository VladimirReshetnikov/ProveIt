#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error whitehead_exposure.tex
pdflatex -interaction=nonstopmode -halt-on-error whitehead_exposure.tex
pdflatex -interaction=nonstopmode -halt-on-error whitehead_exposure.tex
