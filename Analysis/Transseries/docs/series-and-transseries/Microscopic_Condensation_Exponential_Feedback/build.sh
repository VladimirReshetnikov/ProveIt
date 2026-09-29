#!/bin/sh
# Compile the self-contained article; leave intermediates in build/.
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
  echo "pdflatex is required (install a standard TeX Live distribution)." >&2
  exit 1
}
mkdir -p build
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
      -output-directory=build article.tex >"build/pass-${pass}.log" 2>&1; then
    cat "build/pass-${pass}.log" >&2
    exit 1
  fi
done
cp build/article.pdf article.pdf
printf 'Built article.pdf; logs and intermediate files are in build/.\n'
