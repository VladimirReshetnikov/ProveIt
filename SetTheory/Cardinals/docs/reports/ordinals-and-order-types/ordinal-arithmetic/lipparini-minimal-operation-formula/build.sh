#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v python3 >/dev/null || { echo 'python3 is required' >&2; exit 1; }
command -v pdflatex >/dev/null || { echo 'pdflatex is required' >&2; exit 1; }
mkdir -p results
python3 code/verify.py --seed 20260919 --trials 20000 \
    --output results/verification.json > results/verification.txt
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex \
        > "results/latex-pass-${pass}.log"
done
if grep -Eq 'LaTeX Warning: (Reference|Citation)|There were undefined references|Label\(s\) may have changed|Overfull \\hbox|Overfull \\vbox' article.log; then
    echo 'Review LaTeX warnings in article.log.' >&2
    exit 1
fi
printf 'Verification passed; article.pdf rebuilt.\n'
