#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
latexmk -pdf -interaction=nonstopmode -halt-on-error binary_morphic_fluctuations.tex
