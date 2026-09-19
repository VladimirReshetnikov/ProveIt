#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'pdfLaTeX was not found. Install TeX Live or MiKTeX with the packages listed in README.md.' >&2
  exit 1
}
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error Cofinal_Orbit_Consistency.tex
done
printf '%s\n' 'Built Cofinal_Orbit_Consistency.pdf'
