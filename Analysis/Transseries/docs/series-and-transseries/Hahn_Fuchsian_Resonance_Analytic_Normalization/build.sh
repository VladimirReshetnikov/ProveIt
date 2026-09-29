#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error hahn_fuchsian.tex >/dev/null
done
printf '%s\n' 'Built hahn_fuchsian.pdf'
