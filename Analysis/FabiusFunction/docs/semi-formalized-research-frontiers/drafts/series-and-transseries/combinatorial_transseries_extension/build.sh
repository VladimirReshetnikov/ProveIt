#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
  echo "pdflatex is required (a standard TeX Live installation is sufficient)." >&2
  exit 1
}
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error combinatorial_transseries_and_inverses.tex
done
