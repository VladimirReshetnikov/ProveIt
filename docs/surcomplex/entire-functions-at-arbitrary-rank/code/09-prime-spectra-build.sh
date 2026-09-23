#!/bin/sh
# Rebuild the standalone article and run the exact finite sanity checks.
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
BASE=prime_spectra_at_surreal_infinity
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT HUP INT TERM
cd "$HERE"
command -v pdflatex >/dev/null 2>&1 || {
    echo 'pdfLaTeX is required.' >&2; exit 1;
}
for PASS in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory="$TMP" "$BASE.tex" >"$TMP/pass-$PASS.log" 2>&1; then
        cat "$TMP/pass-$PASS.log" >&2
        exit 1
    fi
done
cp "$TMP/$BASE.pdf" "$HERE/$BASE.pdf"
python3 verify_finite.py --json verification_results.json
printf '\nBuilt %s.pdf\n' "$BASE"
