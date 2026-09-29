#!/bin/sh
# Build from this script's directory; no network or shell escape is needed.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
  echo 'pdfLaTeX is required. Install a conventional TeX Live distribution.' >&2
  exit 1
}
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
