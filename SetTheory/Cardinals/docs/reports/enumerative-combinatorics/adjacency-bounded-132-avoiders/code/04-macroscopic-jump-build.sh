#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
command -v pdflatex >/dev/null || { echo 'pdflatex is required' >&2; exit 1; }
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$tmp" article.tex > "$tmp/build-$pass.txt"; then
    cat "$tmp/build-$pass.txt" >&2
    exit 1
  fi
done
cp "$tmp/article.pdf" article.pdf
printf 'Built %s/article.pdf\n' "$PWD"
