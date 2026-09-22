#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v latexmk >/dev/null 2>&1 || {
  printf '%s\n' 'latexmk is required (TeX Live or MiKTeX).' >&2
  exit 1
}
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
