#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
exec latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_lexicographic_orders_further_study.tex
