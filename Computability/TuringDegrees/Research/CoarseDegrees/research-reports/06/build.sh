#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
PYTHON="${PYTHON:-python3}"
command -v "$PYTHON" >/dev/null || { echo "Python not found: $PYTHON" >&2; exit 1; }
command -v pdflatex >/dev/null || { echo "pdfLaTeX is required to build the article." >&2; exit 1; }
"$PYTHON" checks/verify_finite_core.py | tee checks/results.txt
mkdir -p .build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build \
        coarse_minimal_pair_attack.tex > ".build/pass-${pass}.txt" 2>&1 || {
            cat ".build/pass-${pass}.txt" >&2
            exit 1
        }
done
cp .build/coarse_minimal_pair_attack.pdf coarse_minimal_pair_attack.pdf
echo "Built coarse_minimal_pair_attack.pdf"
