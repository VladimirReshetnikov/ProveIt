#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'Error: pdflatex is required. Install a standard LaTeX distribution.' >&2
    exit 1
}
mkdir -p .latex-build
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=.latex-build friendly_order_types.tex \
        >".latex-build/pass${pass}.log" 2>&1; then
        cat ".latex-build/pass${pass}.log" >&2
        exit 1
    fi
done
cp .latex-build/friendly_order_types.pdf friendly_order_types.pdf
printf '%s\n' 'Built friendly_order_types.pdf'
