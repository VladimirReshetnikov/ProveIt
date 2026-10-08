#!/bin/sh
set -eu
cd "$(dirname "$0")"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex > /dev/null
done
if grep -E 'Overfull|undefined|Label\(s\) may have changed' manuscript.log; then
  echo 'Review the TeX diagnostics before distributing this build.' >&2
  exit 1
fi
rm -f manuscript.aux manuscript.out manuscript.toc
printf 'Built %s/manuscript.pdf\n' "$PWD"
