#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build tournament_coexistence.tex
cp build/tournament_coexistence.pdf tournament_coexistence.pdf
