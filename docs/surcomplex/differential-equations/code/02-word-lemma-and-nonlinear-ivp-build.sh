#!/bin/sh
set -eu
cd "$(dirname "$0")"
if ! command -v latexmk >/dev/null 2>&1; then
    printf '%s\n' 'latexmk is required; use a LaTeX installation with the packages named in article.tex.' >&2
    exit 127
fi
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
