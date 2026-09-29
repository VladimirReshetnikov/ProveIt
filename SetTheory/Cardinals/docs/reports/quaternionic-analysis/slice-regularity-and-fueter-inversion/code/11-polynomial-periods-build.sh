#!/usr/bin/env sh
# Build the article; keep the failing pass log for diagnostics.
set -eu
cd "$(dirname "$0")"
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error article.tex > "build-pass-${pass}.log"; then
    tail -n 60 "build-pass-${pass}.log" >&2
    exit 1
  fi
done
rm -f article.aux article.log article.out article.toc \
  build-pass-1.log build-pass-2.log build-pass-3.log
printf '%s\n' 'Built article.pdf'
