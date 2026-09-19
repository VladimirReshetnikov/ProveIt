#!/bin/sh
set -eu
cd -- "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'pdfLaTeX is required. Install TeX Live or MiKTeX with the source packages.' >&2
  exit 1
fi
name=Large_Cardinals_Research_Continuation
mkdir -p build
for pass in 1 2 3; do
  pdflatex -file-line-error -interaction=nonstopmode -halt-on-error \
    -output-directory=build "$name.tex"
done
cp "build/$name.pdf" "$name.pdf"
printf '\nBuilt %s.pdf\n' "$name"
