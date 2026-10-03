#!/bin/sh
# Build outside the sealed inventory and copy only the requested PDF into it.
set -eu
cd "$(dirname "$0")"
ROOT=$(pwd)
BUILD=$(mktemp -d "/tmp/report26-tex.XXXXXX")
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
for pass in 1 2 3; do
  pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" report26.tex >"$BUILD/compile-$pass.log" 2>&1 || { tail -80 "$BUILD/compile-$pass.log"; exit 1; }
done
cp "$BUILD/report26.pdf" report26.pdf
if grep -E 'Overfull|Underfull|Warning' "$BUILD/report26.log"; then :; fi
printf '%s\n' 'Built report26.pdf; temporary build files removed; review and reseal before delivery'
