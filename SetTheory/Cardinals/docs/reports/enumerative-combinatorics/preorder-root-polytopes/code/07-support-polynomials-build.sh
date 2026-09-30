#!/bin/sh
# Rebuild the standalone article without shell escape or a separate bibliography.
set -eu
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build \
        support_polynomials.tex > "build/pass-${pass}.log"
done
if grep -Eq 'undefined references|Citation .* undefined|Reference .* undefined|Overfull' build/support_polynomials.log; then
    echo 'Build completed with unresolved references or overfull boxes; inspect build/support_polynomials.log.' >&2
    exit 1
fi
cp build/support_polynomials.pdf support_polynomials.pdf
printf '%s\n' 'Built support_polynomials.pdf'
