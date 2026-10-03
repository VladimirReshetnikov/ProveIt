#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error infinite_pressure_sign_changes.tex > "build-pass-$pass.log"
done

