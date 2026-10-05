#!/bin/sh
set -eu
cd "$(dirname "$0")"
latexmk -pdf -interaction=nonstopmode -halt-on-error a261781_hankel_zero_laws.tex
