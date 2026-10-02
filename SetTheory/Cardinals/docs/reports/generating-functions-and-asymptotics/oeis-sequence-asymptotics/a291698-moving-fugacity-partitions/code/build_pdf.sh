#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$ROOT/output/pdf"
# Normal complete TeX installations need no workaround. Some managed images
# contain the TeX source tree but omit generated formats and filename indexes.
if ! kpsewhich pdflatex.fmt >/dev/null || ! kpsewhich article.cls >/dev/null; then
  CACHE="$ROOT/.tex-cache"
  mkdir -p "$CACHE/var/web2c/pdftex" "$CACHE/config/tex/generic/config"
  export TEXMFVAR="$CACHE/var" TEXMFCONFIG="$CACHE/config"
  export TEXMF="{$TEXMFCONFIG,$TEXMFVAR,/etc/texmf,/usr/share/texmf,/usr/share/texlive/texmf-dist}"
  export TEXFORMATS="$TEXMFVAR/web2c/pdftex"
  printf 'english hyphen.tex\n' > "$TEXMFCONFIG/tex/generic/config/language.dat"
  if [ ! -f "$TEXFORMATS/pdflatex.fmt" ]; then
    (cd "$TEXFORMATS" && pdftex -ini -etex -jobname=pdflatex -progname=pdflatex '*pdflatex.ini' > format.log 2>&1)
  fi
fi
cd "$ROOT"
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory output/pdf moving-fugacity-report.tex > "output/pdf/build-pass-$pass.log" 2>&1
done
if grep -E 'Overfull|Undefined control sequence|LaTeX Error' output/pdf/build-pass-2.log; then
  echo 'Build has a layout or TeX error' >&2
  exit 1
fi
printf '%s\n' "$ROOT/output/pdf/moving-fugacity-report.pdf"
