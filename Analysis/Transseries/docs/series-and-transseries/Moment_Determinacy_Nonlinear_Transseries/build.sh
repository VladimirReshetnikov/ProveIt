#!/bin/sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'Error: pdflatex is required (for example, from TeX Live).' >&2
    exit 1
}
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        moment_determinacy_transseries.tex
done
printf '%s\n' 'Built moment_determinacy_transseries.pdf'
