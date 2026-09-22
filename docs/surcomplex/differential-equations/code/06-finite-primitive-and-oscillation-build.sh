#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v latexmk >/dev/null 2>&1; then
    printf '%s\n' 'latexmk is required; install a LaTeX distribution with latexmk.' >&2
    exit 2
fi
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
