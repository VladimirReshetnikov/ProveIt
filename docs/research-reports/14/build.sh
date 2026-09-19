#!/bin/sh
# Build the self-contained source without leaving auxiliary files beside it.
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'Error: pdflatex is required (TeX Live or MiKTeX).' >&2
    exit 1
fi
mkdir -p .build
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
        -output-directory=.build Cardinals_Continuation.tex \
        > ".build/pass${pass}.stdout" 2>&1; then
        tail -n 70 ".build/pass${pass}.stdout" >&2
        exit 1
    fi
done
cp .build/Cardinals_Continuation.pdf Cardinals_Continuation.pdf
printf '%s\n' 'Built Cardinals_Continuation.pdf (auxiliary files are in .build/).'
