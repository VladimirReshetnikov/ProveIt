#!/bin/sh
# Run the exact checks, then build both documents.
# No separate BibTeX run is required; the bibliography is inline.
set -eu
cd "$(dirname "$0")"

# 1. The exact finite checks. A failure here stops the build.
if command -v python3 >/dev/null 2>&1; then
    python3 code/verify.py --degree 256 --trials 1000 --output results
elif command -v python >/dev/null 2>&1; then
    python code/verify.py --degree 256 --trials 1000 --output results
else
    printf '%s\n' 'No python3 or python found; skipping the exact checks.' >&2
fi

# 2. The PDFs. latexmk is preferred; three pdflatex passes are the fallback.
if command -v latexmk >/dev/null 2>&1; then
    mkdir -p build
    for name in article short-proof; do
        latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build "$name.tex"
        cp "build/$name.pdf" "$name.pdf"
    done
elif command -v pdflatex >/dev/null 2>&1; then
    for name in article short-proof; do
        pdflatex -interaction=nonstopmode -halt-on-error "$name.tex"
        pdflatex -interaction=nonstopmode -halt-on-error "$name.tex"
        pdflatex -interaction=nonstopmode -halt-on-error "$name.tex"
    done
else
    printf '%s\n' 'Neither latexmk nor pdflatex was found. Install a LaTeX distribution.' >&2
    exit 1
fi
printf '%s\n' 'Built article.pdf and short-proof.pdf.'
