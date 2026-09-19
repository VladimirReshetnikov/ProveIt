#!/usr/bin/env bash
set -euo pipefail

root_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$root_dir"

if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'Error: pdfLaTeX was not found. Install a TeX distribution with the packages listed in README.md.' >&2
  exit 127
fi

name='Cofinal_Orbit_Rigidity'
build_dir="$root_dir/.build"
mkdir -p "$build_dir"

for pass in 1 2 3; do
  printf '\nBuilding pass %s of 3...\n' "$pass"
  if ! pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
      -output-directory="$build_dir" "$name.tex"; then
    printf '\nBuild failed. Inspect %s/%s.log for details.\n' "$build_dir" "$name" >&2
    exit 1
  fi
done

cp -- "$build_dir/$name.pdf" "$root_dir/$name.pdf"
printf '\nBuilt: %s/%s.pdf\nAuxiliary files are in %s.\n' "$root_dir" "$name" "$build_dir"
