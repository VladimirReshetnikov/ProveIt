#!/usr/bin/env bash
set -euo pipefail
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
 pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build a202061-report.tex > .build/compile-$pass.log
done
cp .build/a202061-report.pdf a202061-report.pdf
printf 'Built %s\n' "$PWD/a202061-report.pdf"
