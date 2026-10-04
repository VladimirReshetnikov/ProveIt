#!/usr/bin/env bash
# Build the self-contained LaTeX manuscript. No bibliography processor is needed.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf 'Missing pdflatex. Install a LaTeX distribution with mathpazo, microtype, and cleveref.\n' >&2
  exit 1
fi
work="$(mktemp -d)"
trap 'rm -rf -- "$work"' EXIT
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error \
       -output-directory="$work" article.tex >"$work/pass-$pass.txt" 2>&1; then
    cat "$work/pass-$pass.txt" >&2
    exit 1
  fi
done
if grep -Eq 'Overfull|LaTeX Warning:.*undefined|There were undefined references' "$work/article.log"; then
  grep -nE 'Overfull|Warning' "$work/article.log" >&2
  printf 'The build needs a layout or reference review.\n' >&2
  exit 1
fi
cp -- "$work/article.pdf" article.pdf
printf 'Built %s/article.pdf\n' "$PWD"
