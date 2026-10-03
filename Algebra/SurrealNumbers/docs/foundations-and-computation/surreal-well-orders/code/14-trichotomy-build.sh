#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'pdflatex is required (with the packages listed in article.tex).' >&2
  exit 1
}
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
