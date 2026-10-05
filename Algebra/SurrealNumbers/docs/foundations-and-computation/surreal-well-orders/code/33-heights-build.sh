#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
command -v pdflatex >/dev/null || { echo 'pdflatex is required.' >&2; exit 1; }
mkdir -p .build
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex \
    > ".build/pass${pass}.log" 2>&1 || { cat ".build/pass${pass}.log" >&2; exit 1; }
done
cp .build/article.pdf article.pdf
printf '%s\n' 'Built article.pdf. Bibliography is embedded in article.tex.'
