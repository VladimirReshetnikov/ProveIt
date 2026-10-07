#!/usr/bin/env sh
# Build in a temporary directory so the package is not filled with TeX intermediates.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || { echo 'pdflatex is required' >&2; exit 1; }
command -v python3 >/dev/null 2>&1 || { echo 'Python 3.10+ is required' >&2; exit 1; }
tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT HUP INT TERM
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$tmpdir" \
        odd_order_cube_stability.tex > "$tmpdir/pass-$pass.txt" || {
        cat "$tmpdir/pass-$pass.txt" >&2
        exit 1
    }
done
cp "$tmpdir/odd_order_cube_stability.pdf" ./odd_order_cube_stability.pdf
python3 verification/verify.py
python3 verification/local_checks.py
printf '%s\n' 'PDF built and all full exact checks passed.'
