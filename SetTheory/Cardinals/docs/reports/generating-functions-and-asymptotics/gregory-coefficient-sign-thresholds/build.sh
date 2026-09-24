#!/bin/sh
set -eu
cd "$(dirname "$0")"
PYTHON="${PYTHON:-python3}"
case "${1:-}" in
  ""|--full) ;;
  *) printf '%s\n' "Usage: sh build.sh [--full]" >&2; exit 2 ;;
esac
"$PYTHON" code/verify_exact.py
if [ "${1:-}" = --full ]; then
  "$PYTHON" code/derive_asymptotics.py --output data/asymptotic_coefficients.txt
  "$PYTHON" code/numerical_roots.py
fi
if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' "pdflatex not found; exact verification completed, but PDF build requires TeX." >&2
  exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error gregory_sign_threshold.tex
pdflatex -interaction=nonstopmode -halt-on-error gregory_sign_threshold.tex
