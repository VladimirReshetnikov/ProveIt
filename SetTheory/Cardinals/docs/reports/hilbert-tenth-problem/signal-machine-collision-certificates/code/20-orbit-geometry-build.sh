#!/bin/sh
# Build only in an external directory; never change a sealed release payload.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
OUT=${1:-"$ROOT/../report30-build"}
mkdir -p "$OUT"
OUT=$(CDPATH= cd -- "$OUT" && pwd)
case "$OUT/" in "$ROOT/"*) echo 'Build directory must be outside the release' >&2; exit 1;; esac
BUILD=$(mktemp -d)
trap 'rm -rf "$BUILD"' EXIT HUP INT TERM
if ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
export TEXMFVAR="$BUILD" TEXMFCONFIG="$BUILD" TEXFORMATS="$BUILD:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd "$BUILD" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini >format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : >"$BUILD/pdftex.map"
  for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
    cat "$(kpsewhich "$name")" >>"$BUILD/pdftex.map"
  done
  export TEXFONTMAPS="$BUILD:"
fi
export TZ=UTC SOURCE_DATE_EPOCH=1790985600 FORCE_SOURCE_DATE=1
cd "$ROOT"
for pass in 1 2 3; do
  pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" report30.tex >"$BUILD/pass-$pass.log" 2>&1 || { tail -80 "$BUILD/pass-$pass.log"; exit 1; }
done
if grep -E 'Overfull|undefined references|undefined citations' "$BUILD/report30.log"; then
  echo 'LaTeX layout or reference warning' >&2; exit 1
fi
cp "$BUILD/report30.pdf" "$BUILD/report30.log" "$OUT/"
printf '%s\n' 'PDF build PASS; output directory is external to the release'
