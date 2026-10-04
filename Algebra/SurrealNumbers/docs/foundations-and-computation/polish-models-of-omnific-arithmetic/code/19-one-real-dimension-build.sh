#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
    echo "pdflatex is required (TeX Live or MiKTeX)." >&2; exit 1;
}
command -v python3 >/dev/null 2>&1 || {
    echo "Python 3.10 or later is required for the finite checks." >&2; exit 1;
}
python3 checks/verify_finite.py --output checks/results.json
for pass in 1 2 3; do
    pdflatex -halt-on-error -interaction=nonstopmode one_real_dimension.tex
done
printf '\nBuilt one_real_dimension.pdf and checks/results.json\n'
