#!/bin/sh
# Build the self-contained article, resolving references and the contents.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'Error: pdflatex is not available on PATH.' >&2
    exit 1
fi
for pass in 1 2 3; do
    printf 'pdfLaTeX pass %s of 3\n' "$pass"
    pdflatex -interaction=nonstopmode -halt-on-error surreal_large_cardinals.tex
done
