#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || { echo 'pdflatex is required' >&2; exit 1; }
BIB=''
for candidate in bibtex bibtex8 bibtex.original; do
    if command -v "$candidate" >/dev/null 2>&1; then BIB="$candidate"; break; fi
done
[ -n "$BIB" ] || { echo 'bibtex or bibtex8 is required' >&2; exit 1; }
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
"$BIB" paper
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
printf '\nBuilt paper.pdf\n'
