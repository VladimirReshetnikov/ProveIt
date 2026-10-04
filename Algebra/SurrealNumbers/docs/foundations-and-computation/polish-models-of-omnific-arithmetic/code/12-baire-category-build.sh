#!/bin/sh
# Build without leaving auxiliary files in the package directory.
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdflatex is required (with the LaTeX packages in article.tex).' >&2
    exit 1
fi
BUILD=$(mktemp -d)
trap 'rm -rf "$BUILD"' EXIT HUP INT TERM
cp "$HERE/article.tex" "$BUILD/article.tex"
cd "$BUILD"
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error article.tex >"build-$pass.log" 2>&1; then
        cat "build-$pass.log" >&2
        exit 1
    fi
done
cp article.pdf "$HERE/article.pdf"
printf '%s\n' "Built $HERE/article.pdf"
