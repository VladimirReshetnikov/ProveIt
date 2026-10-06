#!/bin/sh
set -eu
cd "$(dirname "$0")"
command -v python3 >/dev/null 2>&1 || { echo 'python3 is required' >&2; exit 1; }
command -v pdflatex >/dev/null 2>&1 || { echo 'pdfLaTeX is required' >&2; exit 1; }
python3 verify.py > verification.txt
mkdir -p build
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build \
         collision_sensitive_arrangements.tex > "build/pass-${pass}.txt"; then
        cat "build/pass-${pass}.txt" >&2
        exit 1
    fi
done
cp build/collision_sensitive_arrangements.pdf collision_sensitive_arrangements.pdf
printf '%s\n' 'Checks passed; collision_sensitive_arrangements.pdf rebuilt.'
