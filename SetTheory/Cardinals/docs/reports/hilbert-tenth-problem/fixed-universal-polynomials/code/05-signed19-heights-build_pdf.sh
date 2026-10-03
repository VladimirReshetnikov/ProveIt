#!/bin/sh
# Local offline PDF build, no shell escape; outputs stay in the selected build directory.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
BUILD=${1:-$(mktemp -d "${TMPDIR:-/tmp}/report34-pdf-XXXXXX")}
mkdir -p "$BUILD"
BUILD=$(CDPATH= cd -- "$BUILD" && pwd)
case "$BUILD" in "$ROOT"|"$ROOT"/*) echo "Build directory must be outside the release tree" >&2; exit 1;; esac
mkdir -p "$BUILD/tex-cache"
export TEXMFVAR="$BUILD/tex-cache" TEXMFCONFIG="$BUILD/tex-cache" TEXFORMATS="$BUILD/tex-cache:"
if ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd "$BUILD/tex-cache" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini >format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : >"$BUILD/tex-cache/pdftex.map"
  for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
    cat "$(kpsewhich "$name")" >>"$BUILD/tex-cache/pdftex.map"
  done
  export TEXFONTMAPS="$BUILD/tex-cache:"
fi
export TZ=UTC SOURCE_DATE_EPOCH=1790985600 FORCE_SOURCE_DATE=1
cd "$ROOT"
for pass in 1 2 3; do
  pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" Research_Report34.tex >"$BUILD/compile-$pass.log" 2>&1 || { tail -70 "$BUILD/compile-$pass.log"; exit 1; }
done
printf 'Built %s/Research_Report34.pdf\n' "$BUILD"
