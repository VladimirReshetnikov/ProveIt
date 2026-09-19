#!/usr/bin/env sh
set -eu
cd -- "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'pdfLaTeX was not found. Install a TeX distribution first.' >&2
    exit 1
}
mkdir -p _build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=_build Canonical_Tail_Measures.tex
done
cp _build/Canonical_Tail_Measures.pdf Canonical_Tail_Measures.pdf
printf '%s\n' 'Built Canonical_Tail_Measures.pdf'
