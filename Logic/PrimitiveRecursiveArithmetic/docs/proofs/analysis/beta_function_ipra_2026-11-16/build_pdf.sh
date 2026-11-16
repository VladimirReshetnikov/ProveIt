#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")/paper"
latexmk -pdf -interaction=nonstopmode -halt-on-error beta_function_ipra.tex
