#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
if command -v latexmk >/dev/null 2>&1; then
    exec latexmk -pdf -interaction=nonstopmode -halt-on-error birthdays_recover_sets.tex
fi
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "Missing pdfLaTeX. Install a TeX distribution with the packages listed in README.md." >&2
    exit 1
fi
# Repeated passes resolve the table of contents, citations, and cross-references.
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error birthdays_recover_sets.tex
done
