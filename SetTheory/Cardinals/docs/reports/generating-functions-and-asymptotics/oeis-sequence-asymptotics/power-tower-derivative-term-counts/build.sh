#!/usr/bin/env sh
# Build article.pdf.  Three passes: the article has a table of contents and
# cross-references between its parts, so two passes are not enough.
set -eu
cd "$(dirname "$0")"
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
