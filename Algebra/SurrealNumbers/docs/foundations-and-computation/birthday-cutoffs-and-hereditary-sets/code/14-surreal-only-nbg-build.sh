#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v python3 >/dev/null || { echo 'Python 3 is required.' >&2; exit 1; }
command -v pdflatex >/dev/null || { echo 'pdfLaTeX is required.' >&2; exit 1; }
python3 verify_finite.py
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
done
if grep -Eq 'Overfull|undefined references|undefined on input line' article.log; then
  echo 'Review article.log: layout or reference warnings were found.' >&2
  exit 1
fi
printf '\nBuilt article.pdf; finite checks recorded in verification.json.\n'
