#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v latexmk >/dev/null 2>&1; then
    printf '%s\n' 'latexmk is required; install it with a LaTeX distribution.' >&2
    exit 1
fi
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build article.tex
cp build/article.pdf article.pdf
printf '%s\n' 'Built article.pdf'
