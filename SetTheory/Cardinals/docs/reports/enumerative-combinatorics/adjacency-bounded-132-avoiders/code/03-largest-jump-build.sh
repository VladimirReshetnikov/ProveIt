#!/usr/bin/env sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
BUILD=$(mktemp -d)
trap 'rm -rf "$BUILD"' EXIT HUP INT TERM
cd "$ROOT"
for PASS in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory="$BUILD" article.tex > "$BUILD/pass-$PASS.txt" 2>&1 || {
      cat "$BUILD/pass-$PASS.txt"
      exit 1
    }
done
cp "$BUILD/article.pdf" "$ROOT/article.pdf"
printf '%s\n' 'Built article.pdf successfully.'
