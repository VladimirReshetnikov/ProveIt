#!/bin/sh
# Standard TeX Live/MiKTeX installation with Latin Modern and AMS packages.
# Supply normal TEXINPUTS/TEXFONTS environment overrides only if your installation needs them.
set -eu
cd "$(dirname "$0")"
pdflatex -halt-on-error -interaction=nonstopmode report.tex
pdflatex -halt-on-error -interaction=nonstopmode report.tex
