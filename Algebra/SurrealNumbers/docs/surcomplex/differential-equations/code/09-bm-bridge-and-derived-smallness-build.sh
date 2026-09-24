#!/bin/sh
# Build the standalone article; no shell escape or bibliography processor needed.
set -eu
cd "$(dirname "$0")"
if ! command -v latexmk >/dev/null 2>&1; then
  echo "latexmk is required (available in standard TeX Live / MiKTeX installations)." >&2
  exit 1
fi
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
