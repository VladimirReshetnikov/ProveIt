#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
command -v python3 >/dev/null || { echo 'Python 3 is required.' >&2; exit 1; }
command -v pdflatex >/dev/null || { echo 'pdfLaTeX is required (TeX Live or MiKTeX).' >&2; exit 1; }
python3 checks/check_finite.py > checks/run.txt
mkdir -p .build
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex \
    > ".build/pass-${pass}.log" 2>&1 || {
      tail -n 60 ".build/pass-${pass}.log" >&2
      exit 1
    }
done
cp .build/article.pdf article.pdf
if grep -Eq 'undefined references|Citation.*undefined|Reference.*undefined' .build/article.log; then
  echo 'Unresolved references remain; inspect .build/article.log.' >&2
  exit 1
fi
printf 'Built article.pdf; finite checks passed. No infinite theorem was machine-certified.\n'
