#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex > "build-pass-$pass.log"
done
printf 'Built %s/article.pdf\n' "$(pwd)"
