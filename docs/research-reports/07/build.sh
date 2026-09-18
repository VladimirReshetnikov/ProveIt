#!/bin/sh
# Rebuild without leaving LaTeX auxiliary files in the source directory.
set -eu
cd -- "$(dirname -- "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo 'Error: pdflatex is required. Install a TeX distribution first.' >&2
    exit 127
fi
work=$(mktemp -d "${TMPDIR:-/tmp}/large-cardinals-build.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM
name=Large_Cardinals_Continuation
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
         -output-directory="$work" "$name.tex" > "$work/pass-$pass.log" 2>&1; then
        cat "$work/pass-$pass.log" >&2
        exit 1
    fi
done
cp "$work/$name.pdf" "$name.pdf"
printf 'Built %s.pdf\n' "$name"
