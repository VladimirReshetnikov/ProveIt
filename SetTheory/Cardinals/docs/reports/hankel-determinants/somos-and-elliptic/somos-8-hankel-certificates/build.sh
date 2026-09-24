#!/usr/bin/env bash
# Build in a temporary directory; retain only the final article.pdf.
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
  printf 'Error: pdflatex was not found. Install a LaTeX distribution first.\n' >&2
  exit 1
}
tmp="$(mktemp -d)"
trap 'rm -rf -- "$tmp"' EXIT
cd "$root"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory="$tmp" article.tex
done
cp -- "$tmp/article.pdf" "$root/article.pdf"
printf '\nCreated %s/article.pdf\n' "$root"
