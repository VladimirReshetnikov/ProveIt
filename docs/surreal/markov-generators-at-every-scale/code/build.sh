#!/bin/sh
set -eu
cd "$(dirname "$0")"
article=surreal_markov_hierarchies.tex
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -halt-on-error -interaction=nonstopmode "$article"
else
    for pass in 1 2 3; do
        pdflatex -halt-on-error -interaction=nonstopmode "$article"
    done
fi
if grep -E 'undefined references|Citation .* undefined|Reference .* undefined|Overfull \\hbox' surreal_markov_hierarchies.log; then
    echo 'Please inspect the LaTeX log before distributing this build.' >&2
    exit 1
fi
