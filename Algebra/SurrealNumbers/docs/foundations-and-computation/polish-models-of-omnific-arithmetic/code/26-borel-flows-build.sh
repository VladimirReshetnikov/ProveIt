#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
python3 verify.py --json verification_results.json
for pass in 1 2 3; do
    pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error \
        -output-directory=build borel_flows.tex
done
cp build/borel_flows.pdf borel_flows.pdf
printf '\nBuilt borel_flows.pdf. Auxiliary files remain in build/.\n'
