#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf 'Error: pdflatex is required. Install TeX Live or MiKTeX.\n' >&2
  exit 1
fi
name='Finitely_Additive_Kernels'
work=$(mktemp -d "${TMPDIR:-/tmp}/cardinals-pdf.XXXXXXXX")
trap 'rm -rf -- "$work"' EXIT
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory="$work" "$name.tex" >"$work/pass-$pass.log" 2>&1; then
    tail -n 70 "$work/pass-$pass.log" >&2
    exit 1
  fi
done
cp -- "$work/$name.pdf" "$name.pdf"
printf 'Built %s.pdf\n' "$name"
