#!/bin/sh
# Rebuild without shell escape; keep auxiliary files in build/.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "Error: pdflatex is not installed or is not on PATH." >&2
    exit 1
fi
mkdir -p build
for pass in 1 2 3; do
    echo "pdfLaTeX pass $pass of 3"
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=build article.tex > "build/pass-$pass.txt" 2>&1; then
        tail -n 60 "build/pass-$pass.txt" >&2
        exit 1
    fi
done
cp build/article.pdf article.pdf
printf '\nCreated article.pdf. Build logs are in build/.\n'
