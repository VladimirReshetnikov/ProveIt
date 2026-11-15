#!/bin/sh
set -eu
isoperimetric_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$isoperimetric_root/build/reused" "$isoperimetric_root/build/report"
build_one() {
  isoperimetric_source_dir=$1
  isoperimetric_output_dir=$2
  (
    cd "$isoperimetric_source_dir"
    if command -v latexmk >/dev/null 2>&1; then
      latexmk -pdf -interaction=nonstopmode -halt-on-error \
        -outdir="$isoperimetric_output_dir" isoperimetric_ipra.tex
    else
      pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory="$isoperimetric_output_dir" isoperimetric_ipra.tex
      pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory="$isoperimetric_output_dir" isoperimetric_ipra.tex
      pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory="$isoperimetric_output_dir" isoperimetric_ipra.tex
    fi
  )
}
build_one "$isoperimetric_root/reused" "$isoperimetric_root/build/reused"
cp "$isoperimetric_root/build/reused/isoperimetric_ipra.pdf" \
   "$isoperimetric_root/reused/isoperimetric_ipra.pdf"
build_one "$isoperimetric_root/report" "$isoperimetric_root/build/report"
cp "$isoperimetric_root/build/report/isoperimetric_ipra.pdf" \
   "$isoperimetric_root/isoperimetric_ipra.pdf"

