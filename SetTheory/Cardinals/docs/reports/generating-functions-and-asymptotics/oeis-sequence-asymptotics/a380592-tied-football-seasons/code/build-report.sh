#!/usr/bin/env bash
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT/report"
BUILD="$ROOT/replay_outputs/latex"
mkdir -p "$BUILD"
# Ordinary TeX installations need no repair. The fallback also supports a
# read-only Debian TeX tree whose generated filename database is absent.
if [[ -z "${TEXMF:-}" ]] && [[ -d /usr/share/texlive/texmf-dist ]] && ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
fi
export TEXMFVAR="$BUILD"
export TEXMFCONFIG="$BUILD"
export TEXFORMATS="$BUILD:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd "$BUILD" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini > format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : > "$BUILD/pdftex.map"
  for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
    map=$(kpsewhich "$name") || { echo "Missing font map $name" >&2; exit 1; }
    cat "$map" >> "$BUILD/pdftex.map"
  done
  export TEXFONTMAPS="$BUILD:"
fi
export SOURCE_DATE_EPOCH=1790899200
export FORCE_SOURCE_DATE=1
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" tied-football-asymptotics.tex > "$BUILD/compile-$pass.log"
done
cp "$BUILD/tied-football-asymptotics.pdf" "$ROOT/tied-football-asymptotics.pdf"
printf 'Built %s\n' "$ROOT/tied-football-asymptotics.pdf"
