#!/bin/sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
  echo 'pdfLaTeX is required; install a LaTeX distribution.' >&2
  exit 1
}
mkdir -p .build
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build \
    two_derivations.tex
 done
cp .build/two_derivations.pdf two_derivations.pdf
printf '\nBuilt two_derivations.pdf\n'
