#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=build article.tex > "build/pass-${pass}.stdout"
done
cp build/article.pdf article.pdf
printf 'Built article.pdf; TeX logs are in build/.\n'
