#!/usr/bin/env bash
# Compile in an isolated temporary directory; never write into the source tree.
set -euo pipefail
if [[ $# -ne 1 || ! -d "$1" ]]; then
  echo 'Usage: bash build.sh EXISTING_OUTPUT_DIRECTORY' >&2
  exit 2
fi
src=$(cd -- "$(dirname -- "$0")" && pwd -P)
out=$(cd -- "$1" && pwd -P)
if [[ "$out/" == "$src/"* ]]; then
  echo "Output directory must be outside the source package" >&2
  exit 2
fi
if [[ -e "$out/Report130.pdf" || -e "$out/Report130.log" ]]; then
  echo 'Refusing to overwrite existing PDF or log outputs' >&2
  exit 2
fi
work=$(mktemp -d "${TMPDIR:-/tmp}/report130-build.XXXXXXXX")
trap 'rm -rf -- "$work"' EXIT
export SOURCE_DATE_EPOCH=1790899200 FORCE_SOURCE_DATE=1
if [[ -d /usr/share/texlive/texmf-dist && -d /usr/share/texmf ]]; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
export TEXMFVAR="$work/texmf-var" TEXMFCONFIG="$work/texmf-config"
export TEXFORMATS="$work//:" TEXINPUTS="$src//:"
(
  cd -- "$work"
  pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex pdflatex.ini > format.stdout
  for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -jobname=Report130 \
      '\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report130.tex}' > "pass-$pass.stdout"
  done
)
if grep -E 'Overfull|undefined references|undefined citations' "$work/Report130.log"; then
  echo 'Build failed layout/reference checks' >&2
  exit 1
fi
cp -- "$work/Report130.pdf" "$out/Report130.pdf"
cp -- "$work/Report130.log" "$out/Report130.log"
printf 'Built %s/Report130.pdf\n' "$out"
