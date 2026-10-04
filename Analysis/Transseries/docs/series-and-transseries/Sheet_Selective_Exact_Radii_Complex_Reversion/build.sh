#!/bin/sh
# Reproduce without overwriting the recorded evidence.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
PYTHON="${PYTHON:-python3}"
mkdir -p build/results build/figures
"$PYTHON" verify.py --out build/results --figures build/figures > build/verification_run.log
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build \
        complex_transseries_reversion.tex > "build/latex_pass_${pass}.log" 2>&1
done
cp build/complex_transseries_reversion.pdf complex_transseries_reversion.pdf
printf '%s\n' 'Built complex_transseries_reversion.pdf; fresh evidence is under build/.'
