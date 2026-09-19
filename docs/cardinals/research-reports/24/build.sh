#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'Error: pdflatex is required. Install TeX Live or MiKTeX.' >&2
    exit 127
fi
for pass in 1 2 3; do
    printf '\nBuild pass %s of 3\n' "$pass"
    pdflatex -interaction=nonstopmode -halt-on-error \
        Cover_Exacting_Stationary_Seeds.tex
done
printf '\nCreated Cover_Exacting_Stationary_Seeds.pdf\n'
