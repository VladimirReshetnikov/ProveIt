#!/bin/sh
# Build from any working directory. No downloads or third-party Python packages.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
PYTHON=${PYTHON:-python3}
command -v "$PYTHON" >/dev/null 2>&1 || { echo "Python 3.10+ is required." >&2; exit 1; }
command -v pdflatex >/dev/null 2>&1 || { echo "pdfLaTeX is required." >&2; exit 1; }
if [ -n "${PYTHONOPTIMIZE:-}" ]; then
    echo "Unset PYTHONOPTIMIZE: verification requires assertions." >&2
    exit 1
fi
mkdir -p data .build
"$PYTHON" code/verify.py > data/verification.log
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=.build article.tex > ".build/pass-${pass}.log" 2>&1; then
        cat ".build/pass-${pass}.log" >&2
        exit 1
    fi
done
cp .build/article.pdf article.pdf
printf '%s\n' 'Verification passed. Built article.pdf.'
