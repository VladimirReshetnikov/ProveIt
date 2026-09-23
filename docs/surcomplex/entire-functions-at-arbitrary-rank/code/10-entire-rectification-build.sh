#!/bin/sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || { echo "pdflatex is required" >&2; exit 1; }
python3 verify.py
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error entire_rectification.tex \
        > "build-pass-${pass}.log" 2>&1 || {
        cat "build-pass-${pass}.log" >&2
        exit 1
    }
done
if grep -E 'Overfull|undefined references|LaTeX Warning: Reference' build-pass-3.log; then
    echo "Review the reported layout or reference warning." >&2
    exit 1
fi
printf '%s\n' 'Built entire_rectification.pdf; finite symbolic checks passed.'
