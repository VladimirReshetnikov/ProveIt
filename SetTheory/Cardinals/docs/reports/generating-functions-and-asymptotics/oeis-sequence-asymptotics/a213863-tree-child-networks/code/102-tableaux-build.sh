#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export SOURCE_DATE_EPOCH=1790899200
export FORCE_SOURCE_DATE=1
mkdir -p build
if [ -d /usr/share/texlive/texmf-dist ]; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
export TEXMFVAR="$PWD/build/texmf-var"
export TEXMFCONFIG="$PWD/build/texmf-config"
export TEXFORMATS="$PWD/build//:"
if [ ! -f build/pdflatex.fmt ]; then
  (cd build && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex pdflatex.ini > format.stdout)
fi
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error '\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{tree_child_amplitude.tex}' > build-pass1.log
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error '\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{tree_child_amplitude.tex}' > build-pass2.log
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error '\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{tree_child_amplitude.tex}' > build-pass3.log
if grep -Eq 'Overfull|undefined references|undefined citations|LaTeX Error|Label[(]s[)] may have changed|Rerun to get cross-references' build-pass3.log; then
  echo 'FAIL: TeX layout/reference errors require review' >&2
  exit 1
fi
printf 'PASS: standalone TeX built without overfull boxes or unresolved references\n'
