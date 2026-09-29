#!/bin/sh
# Build the standalone article; intermediate files remain under build/.
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo 'pdflatex is required. Install TeX Live with the packages listed in article.tex.' >&2
    exit 1
fi
mkdir -p build
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=build article.tex >"build/pass-${pass}.log"; then
        tail -60 "build/pass-${pass}.log" >&2
        exit 1
    fi
done
cp build/article.pdf article.pdf
printf 'Built article.pdf\n'
