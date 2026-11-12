#!/bin/sh
set -eu
cd "$(dirname "$0")"
latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_backward_replacement.tex
