#!/bin/sh
set -eu
# Stable public report date; definitions and checks do not depend on timestamps.
export TZ=UTC
export SOURCE_DATE_EPOCH=1792972800
export FORCE_SOURCE_DATE=1
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
OUT=${1:-"$HERE/ConZFC_Joint_Pell_Certificates_Round23_2026-10-26.pdf"}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT HUP INT TERM
cp "$HERE"/*.tex "$TMP"/
mkdir -p "$HERE/qa/compile_logs"
if [ -d /usr/share/texlive/texmf-dist ] && [ -d /usr/share/texmf ]; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
FMT=''
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd "$TMP" && pdftex -etex -ini -jobname=pdflatex -progname=pdflatex '\input pdflatex.ini' > format-build.log)
  FMT='-fmt=pdflatex.fmt'
  cp "$TMP/format-build.log" "$HERE/qa/compile_logs/"
fi
for pass in 1 2 3; do
  if ! (cd "$TMP" && pdflatex $FMT -interaction=nonstopmode -halt-on-error main.tex > "pass-$pass.log"); then
    cp "$TMP/pass-$pass.log" "$HERE/qa/compile_logs/"
    tail -80 "$TMP/pass-$pass.log" >&2
    exit 1
  fi
  cp "$TMP/pass-$pass.log" "$HERE/qa/compile_logs/"
done
cp "$TMP/main.log" "$HERE/qa/compile_logs/"
if grep -E 'Overfull \\hbox|Overfull \\vbox|undefined references|Reference .* undefined|Citation .* undefined' "$TMP/main.log"; then
  echo 'Report layout or reference check failed' >&2
  exit 1
fi
cp "$TMP/main.pdf" "$OUT"
printf '%s\n' "Built $OUT"
