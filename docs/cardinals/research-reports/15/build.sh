#!/bin/sh
# Build in a temporary directory so no auxiliary files remain beside the source.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'Error: pdflatex is required. Install TeX Live or MiKTeX.' >&2
    exit 1
fi
BUILD=$(mktemp -d "${TMPDIR:-/tmp}/orbit-saturation.XXXXXX")
trap 'rm -rf "$BUILD"' EXIT HUP INT TERM
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory="$BUILD" "$ROOT/Orbit_Saturation.tex" \
        >"$BUILD/pass-$pass.txt" 2>&1; then
        cat "$BUILD/pass-$pass.txt" >&2
        exit 1
    fi
done
cp "$BUILD/Orbit_Saturation.pdf" "$ROOT/Orbit_Saturation.pdf"
printf 'Created %s\n' "$ROOT/Orbit_Saturation.pdf"
