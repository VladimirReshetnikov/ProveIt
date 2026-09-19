#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")/article"
latexmk -pdf -interaction=nonstopmode -halt-on-error tetration_qnewton.tex
