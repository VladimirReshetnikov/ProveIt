#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'pdflatex is required (with the packages listed in article.tex).' >&2
    exit 1
}
for pass in 1 2 3; do
    pdflatex -halt-on-error -interaction=nonstopmode article.tex > "build-pass-${pass}.log"
done
printf '%s\n' 'Built article.pdf. Review article.log for warnings.'
