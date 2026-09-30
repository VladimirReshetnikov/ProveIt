#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'Error: pdflatex is required (install TeX Live with the named packages).' >&2
    exit 1
}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
for pass in 1 2 3; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory="$work" article.tex >"$work/console.log" 2>&1; then
        cat "$work/console.log" >&2
        exit 1
    fi
done
cp "$work/article.pdf" article.pdf
printf '%s\n' 'Built article.pdf'
