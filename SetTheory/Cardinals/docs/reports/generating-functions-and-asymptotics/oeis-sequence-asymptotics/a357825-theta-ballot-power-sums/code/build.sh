#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
command -v "$PYTHON_BIN" >/dev/null 2>&1 || {
    printf '%s\n' 'Python executable not found; set PYTHON appropriately.' >&2
    exit 1
}
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'pdfLaTeX not found; install a LaTeX distribution first.' >&2
    exit 1
}
"$PYTHON_BIN" code/verify.py --all
mkdir -p _build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=_build article.tex
 done
cp _build/article.pdf article.pdf
printf '%s\n' 'Verification and PDF build completed: article.pdf'
