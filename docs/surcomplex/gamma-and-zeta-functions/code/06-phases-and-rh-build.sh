#!/bin/sh
# Build the article without scattering auxiliary files beside the source.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdfLaTeX was not found. Install TeX Live or MiKTeX.' >&2
    exit 1
fi
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=build article.tex > "build/pass-$pass.txt" 2>&1 || {
        cat "build/pass-$pass.txt" >&2
        exit 1
    }
done
cp build/article.pdf article.pdf
printf '%s\n' "Built $ROOT/article.pdf"
