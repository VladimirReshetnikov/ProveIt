#!/bin/sh
# Rebuild the article; keep auxiliary files separate from the deliverable.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "pdfLaTeX is required (for example, a TeX Live installation)." >&2
    exit 1
fi
mkdir -p _build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=_build article.tex > "_build/pass${pass}.stdout"
done
cp _build/article.pdf article.pdf
printf '%s\n' 'Built article.pdf. Auxiliary files are in _build/.'
