#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'pdfLaTeX was not found. Install TeX Live or an equivalent distribution.' >&2
  exit 1
}
mkdir -p .build
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory=.build surreal_self_embeddings.tex
done
cp .build/surreal_self_embeddings.pdf surreal_self_embeddings.pdf
printf '%s\n' 'Built surreal_self_embeddings.pdf'
