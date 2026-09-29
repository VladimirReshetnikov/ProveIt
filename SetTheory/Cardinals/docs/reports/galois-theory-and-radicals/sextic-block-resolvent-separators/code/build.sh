#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
  echo "pdflatex is required (TeX Live or another LaTeX distribution)." >&2
  exit 1
}
mkdir -p .build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex
cp .build/article.pdf article.pdf
printf '\nBuilt article.pdf\n'
