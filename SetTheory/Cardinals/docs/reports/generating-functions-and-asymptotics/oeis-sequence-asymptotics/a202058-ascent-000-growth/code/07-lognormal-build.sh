#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export SOURCE_DATE_EPOCH=1790899200 FORCE_SOURCE_DATE=1 TZ=UTC
mkdir -p build
if [[ -z "${TEXMF:-}" ]] && [[ -d /usr/share/texlive/texmf-dist ]] && ! kpsewhich article.cls >/dev/null 2>&1; then
 export TEXMF='{ /usr/share/texlive/texmf-dist, /usr/share/texmf }'
 export TEXMF="${TEXMF// /}"
fi
export TEXMFVAR="$PWD/build" TEXMFCONFIG="$PWD/build" TEXFORMATS="$PWD/build:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
 (cd build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini > format-build.log)
fi
for pass in 1 2 3; do
 pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build a202058-lognormal.tex > "build/compile-pass${pass}.log"
done
if grep -E 'LaTeX Warning: (Label\(s\) may have changed|There were undefined references)' build/compile-pass3.log >/dev/null; then
 echo 'PDF references did not stabilize after three passes' >&2; exit 1
fi
cp build/a202058-lognormal.pdf a202058-lognormal.pdf
printf 'Built a202058-lognormal.pdf\n'
