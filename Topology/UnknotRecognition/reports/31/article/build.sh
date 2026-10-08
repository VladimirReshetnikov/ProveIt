#!/usr/bin/env sh
set -eu
cd -- "$(dirname -- "$0")"
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error unknot_certified_primitives.tex
