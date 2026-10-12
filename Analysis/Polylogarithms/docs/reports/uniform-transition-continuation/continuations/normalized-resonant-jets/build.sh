#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdflatex is required (for example, install TeX Live).' >&2
    exit 1
fi
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error resonant_polylog_transseries.tex
done
if grep -E 'LaTeX Warning:.*(undefined|multiply)|There were undefined references' resonant_polylog_transseries.log >/dev/null; then
    printf '%s\n' 'The PDF built, but reference warnings remain; inspect the LaTeX log.' >&2
    exit 1
fi
