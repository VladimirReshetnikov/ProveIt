#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
pdflatex -interaction=nonstopmode -halt-on-error article.tex
if command -v "${BIBTEX:-bibtex}" >/dev/null 2>&1; then
  "${BIBTEX:-bibtex}" article
elif command -v bibtex.original >/dev/null 2>&1; then
  bibtex.original article
elif [ ! -s article.bbl ]; then
  echo 'BibTeX is unavailable and the generated article.bbl is missing.' >&2
  exit 1
else
  echo 'Using the supplied article.bbl; rerun BibTeX after bibliography changes.' >&2
fi
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
