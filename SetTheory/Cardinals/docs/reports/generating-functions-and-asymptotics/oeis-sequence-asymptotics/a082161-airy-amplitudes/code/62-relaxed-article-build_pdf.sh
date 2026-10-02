#!/usr/bin/env bash
# Rebuild the article without changing any manifest-bound input.
set -euo pipefail
ARTICLE_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$ARTICLE_DIR/.." && pwd)"
OUT="${1:-$ROOT/output/article}"
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"
case "$OUT/" in "$ROOT/output/"*) ;; *) printf 'Output must be beneath package output/.\n' >&2; exit 1;; esac
if ! command -v pdflatex >/dev/null || ! command -v kpsewhich >/dev/null; then
  printf 'A TeX distribution with pdfLaTeX is required.\n' >&2; exit 1
fi
cd "$OUT"
mkdir -p .build
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1 || ! kpsewhich pdftex.map >/dev/null 2>&1; then
  export TEXMF="$(kpsewhich -var-value=TEXMF | sed 's/!!//g')"
  export TEXMFVAR="$OUT/.build/texmf-var"
  export TEXMFCONFIG="$OUT/.build/texmf-config"
  export TEXMFCACHE="$OUT/.build/texmf-cache"
  export TEXFORMATS="$OUT/.build:"
  if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
    (cd .build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini > format-build.log)
  fi
  if ! kpsewhich pdftex.map >/dev/null 2>&1; then
    : > .build/pdftex.map
    for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
      map="$(kpsewhich "$name")"; cat "$map" >> .build/pdftex.map
    done
    export TEXFONTMAPS="$OUT/.build:"
  fi
fi
for pass in 1 2 3; do
 pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build "$ARTICLE_DIR/relaxed-binary-trees.tex" > ".build/compile-$pass.log"
done
cp .build/relaxed-binary-trees.pdf relaxed-binary-trees.pdf
printf 'Built %s\n' "$OUT/relaxed-binary-trees.pdf"
