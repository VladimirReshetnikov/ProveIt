#!/usr/bin/env bash
# Build article.pdf without leaving TeX intermediates in the source folder.
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
if ! command -v pdflatex >/dev/null 2>&1; then
  echo 'pdflatex is required. Install a TeX distribution with the packages in article.tex.' >&2
  exit 1
fi
build=$(mktemp -d "${TMPDIR:-/tmp}/frechet-paper.XXXXXXXX")
trap 'rm -rf -- "$build"' EXIT
cd -- "$root"
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory="$build" article.tex >"$build/pass${pass}.stdout" 2>&1; then
    cat "$build/pass${pass}.stdout" >&2
    exit 1
  fi
done
if grep -Eq 'undefined references|undefined citations|Overfull' "$build/article.log"; then
  grep -E 'undefined references|undefined citations|Overfull' "$build/article.log" >&2
  exit 1
fi
cp -- "$build/article.pdf" "$root/article.pdf"
printf 'Created %s\n' "$root/article.pdf"
