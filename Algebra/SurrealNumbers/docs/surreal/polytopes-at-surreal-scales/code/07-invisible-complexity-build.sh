#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
export TERM="${TERM:-dumb}"
python verification/verify.py
latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_polytopes.tex
