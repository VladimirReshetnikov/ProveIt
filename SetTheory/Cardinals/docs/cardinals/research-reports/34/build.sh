#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || {
    printf '%s\n' 'pdflatex was not found. Install TeX Live or MiKTeX and retry.' >&2
    exit 1
}
pdflatex -interaction=nonstopmode -halt-on-error Prikry_Choice_Gap.tex
pdflatex -interaction=nonstopmode -halt-on-error Prikry_Choice_Gap.tex
