#!/bin/sh
# Rebuild the article and rerun its explicitly limited finite checks.
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'pdflatex is required; install a LaTeX distribution with the preamble packages.' >&2
  exit 1
}
command -v python3 >/dev/null 2>&1 || {
  printf '%s\n' 'Python 3.10 or later is required for the finite checks.' >&2
  exit 1
}
mkdir -p build data
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build \
    omnific_set_sized_algebra.tex
 done
cp build/omnific_set_sized_algebra.pdf omnific_set_sized_algebra.pdf
python3 code/check_finite_identities.py --output data/finite_checks.json
