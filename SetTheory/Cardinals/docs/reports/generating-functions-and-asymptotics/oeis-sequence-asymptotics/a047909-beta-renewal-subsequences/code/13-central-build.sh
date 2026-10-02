#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
if [[ -z "${TEXMF:-}" ]] && [[ -d /usr/share/texlive/texmf-dist ]] && ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
fi
export TEXMFVAR="$PWD/build/texmf-var"
export TEXMFCONFIG="$PWD/build/texmf-config"
export TEXFORMATS="$PWD/build:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini > format-build.log)
fi
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build beta-renewal-asymptotics.tex > "build/compile-$pass.log"
done
OUTPUT_PDF="${OUTPUT_PDF:-$PWD/beta-renewal-asymptotics.pdf}"
cp build/beta-renewal-asymptotics.pdf "$OUTPUT_PDF"
printf 'Built %s\n' "$OUTPUT_PDF"
