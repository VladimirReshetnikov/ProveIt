#!/usr/bin/env bash
# Compile only the authored report. Never compile or execute upstream code.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="${1:-$ROOT/build-report}"
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"
export SOURCE_DATE_EPOCH=1793059200 FORCE_SOURCE_DATE=1 TZ=UTC
# Explicit system TeX paths avoid a machine-local texmf configuration dependency.
export TEXINPUTS=".:/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:"
export TEXFORMATS="$OUT/texcache//:"
export TEXMFVAR="$OUT/texcache/var" TEXMFCONFIG="$OUT/texcache/config"
export TEXFONTMAPS="$OUT/texcache//:/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//:"
export TFMFONTS='/usr/share/texmf/fonts/tfm//:/usr/share/texlive/texmf-dist/fonts/tfm//:'
export T1FONTS='/usr/share/texmf/fonts/type1//:/usr/share/texlive/texmf-dist/fonts/type1//:'
export VFFONTS='/usr/share/texmf/fonts/vf//:/usr/share/texlive/texmf-dist/fonts/vf//:'
export ENCFONTS='/usr/share/texmf/fonts/enc//:/usr/share/texlive/texmf-dist/fonts/enc//:'
mkdir -p "$OUT/texcache"
cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map > "$OUT/texcache/pdftex.map"
if [ ! -f "$OUT/texcache/pdflatex.fmt" ]; then
 (cd "$OUT/texcache"; pdftex -ini -etex -jobname=pdflatex -progname=pdflatex pdflatex.ini > format.log)
fi
cd "$ROOT/report"
for pass in 1 2 3; do
 pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory "$OUT" report.tex > "$OUT/pass-$pass.log"
done
pdftotext -layout "$OUT/report.pdf" "$OUT/report.txt"
pdfinfo "$OUT/report.pdf" > "$OUT/pdfinfo.txt"
printf 'Built %s\n' "$OUT/report.pdf"
