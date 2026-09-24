#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v pdflatex >/dev/null || { echo 'pdfLaTeX is required.' >&2; exit 1; }
workdir="$(mktemp -d)"
trap 'rm -rf "$workdir"' EXIT
for pass in 1 2; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory="$workdir" sparse_error_minimal_pairs.tex \
        > "$workdir/pass${pass}.txt" 2>&1 || {
        cat "$workdir/pass${pass}.txt" >&2
        exit 1
    }
done
cp "$workdir/sparse_error_minimal_pairs.pdf" sparse_error_minimal_pairs.pdf
if grep -Eq 'Overfull|undefined references|undefined citations' \
        "$workdir/sparse_error_minimal_pairs.log"; then
    echo 'Build succeeded, but inspect these layout/reference warnings:' >&2
    grep -E 'Overfull|undefined references|undefined citations' \
        "$workdir/sparse_error_minimal_pairs.log" >&2
fi
printf 'Built %s\n' "$(pwd)/sparse_error_minimal_pairs.pdf"
