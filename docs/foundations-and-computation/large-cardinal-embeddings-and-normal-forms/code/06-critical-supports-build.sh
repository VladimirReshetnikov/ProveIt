#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if command -v latexmk >/dev/null 2>&1; then
  exec latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
elif command -v pdflatex >/dev/null 2>&1; then
  for run in 1 2 3; do
    pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error article.tex
  done
else
  printf '%s\n' 'Install TeX Live (including pdflatex and the packages listed in README.md).' >&2
  exit 127
fi
