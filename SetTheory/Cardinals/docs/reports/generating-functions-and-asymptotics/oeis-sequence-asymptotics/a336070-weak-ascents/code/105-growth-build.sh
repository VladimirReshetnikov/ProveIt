#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export SOURCE_DATE_EPOCH=1790899200
export FORCE_SOURCE_DATE=1
mkdir -p build qa
if [ -d /usr/share/texlive/texmf-dist ]; then
 export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
export TEXMFVAR="$PWD/build/texmf-var"
export TEXMFCONFIG="$PWD/build/texmf-config"
export TEXFORMATS="$PWD/build//:"
if [ ! -f build/pdflatex.fmt ]; then
 (cd build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex pdflatex.ini > format.stdout)
fi
for pass in 1 2 3; do
 pdflatex -interaction=nonstopmode -halt-on-error -file-line-error '\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{report105.tex}' > "qa/build-pass${pass}.log"
done
if grep -Eq 'Overfull|undefined references|undefined citations|LaTeX Error|Label[(]s[)] may have changed|Rerun to get cross-references' qa/build-pass3.log; then
 echo 'FAIL: TeX layout/reference errors require review' >&2
 grep -E 'Overfull|undefined|Warning|Error' qa/build-pass3.log >&2
 exit 1
fi
printf 'PASS: TeX built without overfull boxes or unresolved references\n'
