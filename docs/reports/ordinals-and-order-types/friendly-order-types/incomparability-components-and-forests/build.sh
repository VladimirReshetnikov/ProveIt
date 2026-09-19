#!/usr/bin/env sh
# Compile without assuming that latexmk or a particular BibTeX executable exists.
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
  echo "error: pdflatex is required (for example, from TeX Live)." >&2
  exit 1
fi
BIBTEX=""
for candidate in bibtex bibtex8 bibtexu; do
  if command -v "$candidate" >/dev/null 2>&1; then
    BIBTEX="$candidate"
    break
  fi
done
if [ -z "$BIBTEX" ]; then
  echo "error: bibtex, bibtex8, or bibtexu is required." >&2
  exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error article.tex
"$BIBTEX" article
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
