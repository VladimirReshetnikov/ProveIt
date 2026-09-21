#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_surcomplex_cas.tex
