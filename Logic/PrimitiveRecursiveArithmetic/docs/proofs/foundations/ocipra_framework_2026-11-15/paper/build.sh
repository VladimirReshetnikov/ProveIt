#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

cd "$HERE"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory="$TMP" ocipra_framework.tex \
    > "$ROOT/validation/pdflatex_pass${pass}.log" 2>&1
done

cp "$TMP/ocipra_framework.pdf" "$HERE/ocipra_framework.pdf"
cp "$TMP/ocipra_framework.log" "$ROOT/validation/pdflatex_final.log"
pdfinfo "$HERE/ocipra_framework.pdf" > "$ROOT/validation/pdfinfo.txt"

if grep -Eiq 'undefined references|citation.*undefined|reference.*undefined|overfull \\hbox' \
    "$ROOT/validation/pdflatex_final.log"; then
  echo "PDF build log contains unresolved references or overfull boxes" >&2
  exit 1
fi
