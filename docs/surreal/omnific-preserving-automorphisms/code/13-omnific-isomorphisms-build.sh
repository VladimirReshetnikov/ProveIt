#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
for tool in python3 pdflatex; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'Required executable not found: %s\n' "$tool" >&2
    exit 1
  fi
done
python3 "$ROOT/code/verify.py"
BUILD="$(mktemp -d)"
trap 'rm -rf -- "$BUILD"' EXIT
cp -- "$ROOT/article.tex" "$BUILD/article.tex"
for pass in 1 2 3; do
  if ! (cd -- "$BUILD" && pdflatex -interaction=nonstopmode -halt-on-error article.tex > "pass-$pass.log" 2>&1); then
    cat -- "$BUILD/pass-$pass.log" >&2
    exit 1
  fi
done
if grep -Eq 'undefined references|Citation .* undefined|Reference .* undefined|Overfull \\hbox' "$BUILD/article.log"; then
  grep -E -A3 'undefined|Overfull' "$BUILD/article.log" >&2
  printf 'Build requires cross-reference or layout review.\n' >&2
  exit 1
fi
cp -- "$BUILD/article.pdf" "$ROOT/article.pdf"
printf 'Built %s\n' "$ROOT/article.pdf"
