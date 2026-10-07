#!/bin/sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
    echo 'pdflatex is required to build this article.' >&2
    exit 1
}
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error gowers_section7_refinements.tex
done
