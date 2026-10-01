#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
  echo 'pdflatex is required (with the LaTeX packages listed in README.md).' >&2
  exit 1
}
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error article.tex
