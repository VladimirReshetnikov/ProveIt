#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
PYTHON="${PYTHON:-python3}"
PDFLATEX="${PDFLATEX:-pdflatex}"
command -v "$PYTHON" >/dev/null || { echo "Python executable not found: $PYTHON" >&2; exit 127; }
command -v "$PDFLATEX" >/dev/null || { echo "pdfLaTeX executable not found: $PDFLATEX" >&2; exit 127; }
mkdir -p build
"$PYTHON" code/verify.py --output build/verification.json > build/verification.log
for pass in 1 2 3; do
    "$PDFLATEX" -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > "build/latex-pass-${pass}.log" 2>&1 || {
        cat "build/latex-pass-${pass}.log" >&2
        exit 1
    }
done
printf '%s\n' 'Built build/article.pdf and build/verification.json'
