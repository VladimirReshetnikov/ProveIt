#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'pdflatex is required (standard TeX Live or a compatible installation).' >&2
    exit 1
}
mkdir -p _build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=_build \
        coarse_degree_attack.tex > "_build/pass${pass}.stdout" 2>&1 || {
        cat "_build/pass${pass}.stdout" >&2
        exit 1
    }
done
if grep -E 'undefined references|undefined citations|Citation .* undefined|Reference .* undefined' \
    _build/coarse_degree_attack.log >/dev/null; then
    printf '%s\n' 'Build left unresolved references; inspect _build/coarse_degree_attack.log.' >&2
    exit 1
fi
cp _build/coarse_degree_attack.pdf coarse_degree_attack.pdf
printf '%s\n' 'Built coarse_degree_attack.pdf'
