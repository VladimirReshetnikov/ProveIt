#!/bin/sh
# Compile the standalone article; intermediates stay in build/.
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'Error: pdflatex is not installed or not on PATH.' >&2
    exit 1
}
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=build article.tex > "build/compile-pass-${pass}.txt"
done
cp build/article.pdf article.pdf
printf '%s\n' 'Built article.pdf.'
