#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
command -v pdflatex >/dev/null || { echo "pdfLaTeX is required." >&2; exit 1; }
command -v python3 >/dev/null || { echo "Python 3.10 or later is required." >&2; exit 1; }
python3 verify_finite.py --output verification_results.json
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
 done
if grep -Eq 'undefined references|Citation .* undefined|Overfull' article.log; then
    echo "The build completed but has unresolved references or layout overflow; inspect article.log." >&2
    exit 1
fi
printf '\nBuilt article.pdf and regenerated verification_results.json.\n'
