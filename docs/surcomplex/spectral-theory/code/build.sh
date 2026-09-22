#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
