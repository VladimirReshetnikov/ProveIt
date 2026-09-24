#!/bin/sh
# Rebuild the self-contained article and run the exact finite checks.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
    echo "pdfLaTeX is required; install TeX Live or MiKTeX." >&2
    exit 1
}
command -v python3 >/dev/null 2>&1 || {
    echo "Python 3.10 or later is required for the finite checks." >&2
    exit 1
}
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=build surcomplex_exponential_kernels.tex
 done
cp build/surcomplex_exponential_kernels.pdf surcomplex_exponential_kernels.pdf
python3 verify.py --output verification_results.json
