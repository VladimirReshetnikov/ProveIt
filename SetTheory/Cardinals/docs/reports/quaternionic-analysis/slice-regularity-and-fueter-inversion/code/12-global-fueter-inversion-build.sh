#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
        -output-directory=build article.tex > "build/pass${pass}.txt"
done
cp build/article.pdf article.pdf
printf 'Built article.pdf\n'
