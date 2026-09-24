#!/usr/bin/env bash
# Build the article and run finite checks. No network access is performed.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
python3 verify.py --output verification.json
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
elif command -v pdflatex >/dev/null 2>&1; then
    for pass in 1 2 3; do
        pdflatex -interaction=nonstopmode -halt-on-error article.tex
    done
else
    printf '%s\n' 'Install a TeX distribution providing pdflatex (latexmk recommended).' >&2
    exit 1
fi
if grep -Eq 'Overfull \\hbox|Overfull \\vbox|There were undefined references|There were undefined citations' article.log; then
    printf '%s\n' 'Build completed with layout or reference warnings; inspect article.log.' >&2
    exit 2
fi
printf '%s\n' 'Built article.pdf. Finite checks are not proof verification.'
