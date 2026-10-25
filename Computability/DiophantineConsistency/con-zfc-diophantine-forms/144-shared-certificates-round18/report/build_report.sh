#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
OUT=${1:-"$HERE/ConZFC_Shared_Certificates_Round18_2026-10-25.pdf"}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT HUP INT TERM
cp "$HERE"/*.tex "$TMP"/
if [ -d /usr/share/texlive/texmf-dist ] && [ -d /usr/share/texmf ]; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
FMT=''
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd "$TMP" && pdftex -etex -ini -jobname=pdflatex -progname=pdflatex '\input pdflatex.ini' > format-build.log)
  FMT='-fmt=pdflatex.fmt'
fi
for pass in 1 2 3; do
  if ! (cd "$TMP" && pdflatex $FMT -interaction=nonstopmode -halt-on-error main.tex > "pass-$pass.log"); then
    tail -80 "$TMP/pass-$pass.log" >&2
    exit 1
  fi
done
if grep -E 'Overfull \\hbox|undefined references|Reference .* undefined|Citation .* undefined' "$TMP/main.log"; then
  echo 'Report layout or reference check failed' >&2
  exit 1
fi
cp "$TMP/main.pdf" "$OUT"
printf '%s\n' "Built $OUT"
