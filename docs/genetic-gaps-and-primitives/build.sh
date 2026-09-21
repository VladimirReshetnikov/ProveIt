#!/usr/bin/env sh
# Rebuild the two papers and run exact finite checks. No network access needed.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if command -v python3 >/dev/null 2>&1; then
    PYTHON=python3
elif command -v python >/dev/null 2>&1; then
    PYTHON=python
else
    echo 'Python 3.9 or later is required.' >&2
    exit 1
fi
"$PYTHON" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 9) else "Python 3.9 or later is required.")'
"$PYTHON" code/verify.py
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
    latexmk -pdf -interaction=nonstopmode -halt-on-error short_proof.tex
elif command -v pdflatex >/dev/null 2>&1; then
    for file in article.tex short_proof.tex; do
        for pass in 1 2 3; do
            pdflatex -interaction=nonstopmode -halt-on-error "$file"
        done
    done
else
    echo 'Install a TeX distribution with pdfLaTeX to rebuild the PDFs.' >&2
    exit 1
fi
printf '\nBuilt article.pdf and short_proof.pdf; exact finite checks passed.\n'
