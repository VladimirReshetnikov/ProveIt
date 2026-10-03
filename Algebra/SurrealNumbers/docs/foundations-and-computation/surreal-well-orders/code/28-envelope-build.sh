#!/usr/bin/env sh
# Build in a temporary directory, leaving no auxiliary files in the package.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || { echo 'pdflatex is required.' >&2; exit 1; }
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory="$tmp" article.tex >"$tmp/pass-$pass.log" 2>&1; then
        cat "$tmp/pass-$pass.log" >&2
        exit 1
    fi
done
cp "$tmp/article.pdf" article.pdf
printf 'Built article.pdf\n'
if [ "${1:-}" = '--check' ]; then
    command -v python3 >/dev/null 2>&1 || { echo 'python3 is required for checks.' >&2; exit 1; }
    python3 code/finite_checks.py --output data/finite_checks.json
fi
