#!/usr/bin/env bash
# Rebuild article.pdf without leaving auxiliary files in the source directory.
set -euo pipefail
SOURCE_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'Error: pdflatex was not found. Install a LaTeX distribution first.' >&2
    exit 1
fi
BUILD_DIR="$(mktemp -d)"
trap 'rm -rf -- "$BUILD_DIR"' EXIT
cd -- "$SOURCE_DIR"
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory="$BUILD_DIR" article.tex > "$BUILD_DIR/pass-$pass.stdout" 2>&1; then
        cat "$BUILD_DIR/pass-$pass.stdout" >&2
        printf 'Error: LaTeX pass %s failed.\n' "$pass" >&2
        exit 1
    fi
done
if grep -Eq 'undefined references|undefined citations|Label\(s\) may have changed|Overfull' "$BUILD_DIR/pass-3.stdout"; then
    cat "$BUILD_DIR/pass-3.stdout" >&2
    printf '%s\n' 'Error: unresolved references or overfull boxes remain.' >&2
    exit 1
fi
cp -- "$BUILD_DIR/article.pdf" "$SOURCE_DIR/article.pdf"
printf 'Built %s/article.pdf\n' "$SOURCE_DIR"
