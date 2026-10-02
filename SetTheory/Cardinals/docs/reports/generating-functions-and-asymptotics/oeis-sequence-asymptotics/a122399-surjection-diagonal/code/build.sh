#!/usr/bin/env bash
set -euo pipefail
export SOURCE_DATE_EPOCH=1790812800
export FORCE_SOURCE_DATE=1
cd "$(dirname "$0")"
mkdir -p .build
# The explicit TEXMF also supports installations whose filename database is absent.
if [[ -z "${TEXMF:-}" ]] && [[ -d /usr/share/texlive/texmf-dist ]] && ! kpsewhich article.cls >/dev/null 2>&1; then
 export TEXMF='{ /usr/share/texlive/texmf-dist, /usr/share/texmf }'
 export TEXMF="${TEXMF// /}"
fi
export TEXMFVAR="$PWD/.build"
export TEXMFCONFIG="$PWD/.build"
export TEXFORMATS="$PWD/.build:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd .build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini > format-build.log)
fi
for pass in 1 2; do
 pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build a122399-report.tex > .build/compile-$pass.log
done
cp .build/a122399-report.pdf a122399-report.pdf
printf 'Built %s\n' "$PWD/a122399-report.pdf"
