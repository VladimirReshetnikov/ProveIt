#!/usr/bin/env bash
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PYTHON=${PYTHON:-python3}
export PYTHONDONTWRITEBYTECODE=1
export OUTPUT_DIR=${OUTPUT_DIR:-"$ROOT/results"}
mkdir -p "$OUTPUT_DIR"
"$PYTHON" -c 'import sympy, mpmath; print("SymPy",sympy.__version__,"mpmath",mpmath.__version__)'
for SCRIPT in verify.py verify_fixed_range.py check.py sector_check.py stabilization_check.py; do
  printf '\nRunning %s\n' "$SCRIPT"
  "$PYTHON" "$ROOT/code/$SCRIPT" > "$OUTPUT_DIR/${SCRIPT%.py}.log"
done
"$PYTHON" "$ROOT/code/compare_results.py" "$ROOT/expected" "$OUTPUT_DIR"
printf '\nAll exact and numerical replay checks passed\n'
