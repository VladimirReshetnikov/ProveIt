#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "pdflatex is required; install TeX Live or MiKTeX." >&2
    exit 1
fi
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=build article.tex > "build/pass-${pass}.txt" 2>&1 || {
        cat "build/pass-${pass}.txt" >&2
        exit 1
    }
done
cp build/article.pdf article.pdf
printf '%s\n' 'Built article.pdf. Intermediate files are in build/.'
