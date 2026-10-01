#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
command -v pdflatex >/dev/null || { echo 'pdflatex is required.' >&2; exit 1; }
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex > "build-pass-${pass}.log"
done
if grep -Eq 'There were undefined references|multiply defined|Overfull' article.log; then
  echo 'Build completed but a reference/layout warning needs review.' >&2
  exit 2
fi
printf 'Built %s/article.pdf\n' "$PWD"
