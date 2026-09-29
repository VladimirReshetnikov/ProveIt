#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
if ! command -v latexmk >/dev/null 2>&1; then
    printf '%s\n' 'latexmk is required. Install it with a TeX distribution.' >&2
    exit 1
fi
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
