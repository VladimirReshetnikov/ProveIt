#!/bin/sh
# Compile the standalone report with pdfLaTeX.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'Error: pdflatex is not on PATH. Install/configure TeX Live or MiKTeX.' >&2
    exit 1
fi
name='Large_Cardinals_Quotient_Continuation'
mkdir -p .build
for pass in 1 2 3 4; do
    printf '\nCompiling pass %s of 4...\n' "$pass"
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
        -output-directory=.build "$name.tex"
done
cp ".build/$name.pdf" "$name.pdf"
printf '\nCreated %s/%s.pdf\n' "$(pwd)" "$name"
