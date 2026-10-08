#!/bin/sh
# Build the complete article after all packaged TeX sections and figures exist.
set -eu
bundle_root=$(CDPATH= cd "$(dirname "$0")/.." && pwd)
cd "$bundle_root/article"
exec latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
