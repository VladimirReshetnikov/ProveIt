#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v latexmk >/dev/null 2>&1; then
    printf '%s\n' 'latexmk is required. Install it with your TeX distribution.' >&2
    exit 1
fi
latexmk -pdf -interaction=nonstopmode -halt-on-error omnific_integers.tex
