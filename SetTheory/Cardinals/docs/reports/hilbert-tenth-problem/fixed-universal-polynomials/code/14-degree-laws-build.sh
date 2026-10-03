#!/bin/sh
# Rebuild with installed TeX in a separate output directory.
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
OUT=${1:?Usage: sh build.sh OUTPUT_DIRECTORY}
mkdir -p "$OUT"
OUT=$(CDPATH= cd -- "$OUT" && pwd)
RELEASE=$(CDPATH= cd -- "$HERE/.." && pwd)
case "$OUT/" in "$RELEASE/"*) echo 'Output must be outside the release directory' >&2; exit 1;; esac
if ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
export TEXMFVAR="$OUT" TEXMFCONFIG="$OUT" TEXFORMATS="$OUT:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd "$OUT" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini >format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : >"$OUT/pdftex.map"
  for name in lm.map cm.map cmextra.map symbols.map latxfont.map euler.map; do
    cat "$(kpsewhich "$name")" >>"$OUT/pdftex.map"
  done
  export TEXFONTMAPS="$OUT:"
fi
export TZ=UTC SOURCE_DATE_EPOCH=1790985600 FORCE_SOURCE_DATE=1
cd "$OUT"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$OUT" "$HERE/report24.tex" >"$OUT/compile-$pass.log" 2>&1 || { tail -80 "$OUT/compile-$pass.log"; exit 1; }
done
if grep -E 'Overfull|Underfull|Warning' "$OUT/report24.log"; then :; fi
printf 'Built %s/report24.pdf\n' "$OUT"
