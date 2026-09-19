#!/usr/bin/env bash
# Build without leaving auxiliary files beside the deliverables.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'Error: pdflatex is not installed or is not on PATH.' >&2
  exit 127
}
BUILD="$(mktemp -d)"
trap 'rm -rf -- "$BUILD"' EXIT
NAME=Maximal_Width_Uniformization
for PASS in 1 2 3; do
  if ! pdflatex -interaction=nonstopmode -halt-on-error \
       -output-directory="$BUILD" "$ROOT/$NAME.tex" >"$BUILD/pass-$PASS.txt" 2>&1; then
    cat "$BUILD/pass-$PASS.txt" >&2
    exit 1
  fi
done
if grep -Eq 'Undefined control sequence|undefined references|undefined on input|Overfull' \
     "$BUILD/$NAME.log"; then
  printf '%s\n' 'Error: unresolved references or overfull boxes remain.' >&2
  grep -En 'Undefined control sequence|undefined references|undefined on input|Overfull' \
       "$BUILD/$NAME.log" >&2
  exit 1
fi
cp -- "$BUILD/$NAME.pdf" "$ROOT/$NAME.pdf"
printf 'Built %s\n' "$ROOT/$NAME.pdf"
