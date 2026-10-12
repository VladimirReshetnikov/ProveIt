#!/bin/sh
set -eu
cd "$(dirname "$0")"
python scripts/summarize_results.py
python scripts/export_standalone.py
mkdir -p .build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex > .build/pass-$pass.txt
done
cp .build/article.pdf article.pdf
printf '%s\n' 'Built article.pdf and article_standalone.tex'
