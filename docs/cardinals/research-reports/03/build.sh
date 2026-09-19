#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'pdfLaTeX was not found. Install a TeX distribution and add its executables to PATH.' >&2
    exit 127
}
name='Large_Cardinals_Research_Continuation'
mkdir -p _build
for pass in 1 2 3; do
    printf 'pdfLaTeX pass %s/3\n' "$pass"
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
        -output-directory=_build "$name.tex" >"_build/pass-$pass.txt" 2>&1 || {
        tail -n 60 "_build/pass-$pass.txt" >&2
        exit 1
    }
done
cp -- "_build/$name.pdf" "$name.pdf"
printf 'Created %s.pdf\n' "$name"
