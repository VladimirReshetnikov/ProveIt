#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
BUILD="$ROOT/.build"
mkdir -p "$BUILD"
command -v pdflatex >/dev/null || { echo 'pdfLaTeX is required.' >&2; exit 1; }
cd "$ROOT/article"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory="$BUILD" article.tex > "$BUILD/pass-${pass}.txt"
done
if grep -Eq 'Overfull|undefined references|undefined citations' "$BUILD/article.log"; then
  echo 'Build requires layout/reference review; see .build/article.log.' >&2
  exit 1
fi
cp "$BUILD/article.pdf" "$ROOT/article/article.pdf"
printf 'Built %s\n' "$ROOT/article/article.pdf"
