#!/bin/sh
# Rebuild the paper without permitting external shell commands from LaTeX.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"

if ! command -v pdflatex >/dev/null 2>&1; then
    echo "Error: pdflatex is required. Install a TeX distribution with the packages listed in the source preamble." >&2
    exit 1
fi

mkdir -p _build
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape \
        -output-directory=_build Beyond_Finite_Choice.tex \
        > "_build/pass-${pass}.log" 2>&1; then
        echo "LaTeX compilation failed on pass ${pass}:" >&2
        tail -80 "_build/pass-${pass}.log" >&2
        exit 1
    fi
done
cp _build/Beyond_Finite_Choice.pdf Beyond_Finite_Choice.pdf
echo "Built: Beyond_Finite_Choice.pdf"
