#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
command -v pdflatex >/dev/null || { echo 'pdflatex is required.' >&2; exit 1; }
BUILD="$(mktemp -d)"
trap 'rm -rf "$BUILD"' EXIT
for pass in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" \
       "$ROOT/article/distribution_jets.tex" >"$BUILD/pass$pass.log" 2>&1; then
    cat "$BUILD/pass$pass.log" >&2
    exit 1
  fi
done
cp "$BUILD/distribution_jets.pdf" "$ROOT/article/distribution_jets.pdf"
if grep -E 'Overfull|undefined|multiply defined' "$BUILD/pass3.log"; then
  echo 'Review the LaTeX warnings printed above.' >&2
  exit 1
fi
echo "Built $ROOT/article/distribution_jets.pdf"
