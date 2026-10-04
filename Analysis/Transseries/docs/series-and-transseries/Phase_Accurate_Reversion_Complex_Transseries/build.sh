#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'pdflatex is required (TeX Live or an equivalent installation).' >&2
  exit 1
}
mkdir -p build
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
    -output-directory=build article.tex > "build/pdflatex-pass-${pass}.txt"
done
cp build/article.pdf article.pdf
printf '%s\n' 'Built article.pdf. Auxiliary files and logs are under build/.'
