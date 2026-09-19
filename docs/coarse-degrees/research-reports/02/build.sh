#!/usr/bin/env bash
# Run finite checks and compile the manuscript. No jump oracle is simulated.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
BUILD="${BUILD_DIR:-$ROOT/.build}"
command -v python3 >/dev/null || { echo 'Python 3 is required.' >&2; exit 1; }
command -v pdflatex >/dev/null || { echo 'pdflatex is required.' >&2; exit 1; }
mkdir -p "$BUILD"
python3 "$ROOT/checks/check_finite_lemmas.py" --output "$ROOT/checks/results.json"
cd "$ROOT"
if command -v latexmk >/dev/null; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error \
      -outdir="$BUILD" coarse_minimal_pair.tex
else
    for pass in 1 2 3; do
        pdflatex -interaction=nonstopmode -halt-on-error \
          -output-directory="$BUILD" coarse_minimal_pair.tex
    done
fi
cp "$BUILD/coarse_minimal_pair.pdf" "$ROOT/coarse_minimal_pair.pdf"
printf '\nPDF written to %s\n' "$ROOT/coarse_minimal_pair.pdf"
