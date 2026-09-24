#!/bin/sh
# Rebuild the standalone article and rerun finite checks.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'Error: pdflatex is required (install TeX Live or MiKTeX).' >&2
    exit 1
}
command -v python3 >/dev/null 2>&1 || {
    printf '%s\n' 'Error: Python 3.10 or newer is required for verify.py.' >&2
    exit 1
}
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
python3 verify.py > verification.txt
cat verification.txt
printf '%s\n' 'Built article.pdf and reran the finite checks.'
