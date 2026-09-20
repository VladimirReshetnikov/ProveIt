#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
    echo "pdflatex is required; see README.md for package requirements." >&2
    exit 1
}
mkdir -p .build
for pass in 1 2; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=.build report.tex > ".build/pass${pass}.log" 2>&1; then
        tail -60 ".build/pass${pass}.log" >&2
        exit 1
    fi
done
cp .build/report.pdf report.pdf
echo "Built report.pdf"
