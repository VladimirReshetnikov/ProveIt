#!/bin/sh
# Optional: requires SymPy. Separate from the stdlib-only main runner.
set -eu
ROOT=$(CDPATH= cd "$(dirname "$0")" && pwd)
PYTHON=${PYTHON:-python3}
export PYTHONDONTWRITEBYTECODE=1
printf '\n=== Optional exact analytic replay, normal interpreter ===\n'
"$PYTHON" -B "$ROOT/check_analytic_coefficients.py"
printf '\n=== Optional exact analytic replay, optimized interpreter (-O) ===\n'
"$PYTHON" -B -O "$ROOT/check_analytic_coefficients.py"
printf '\nPASS: optional analytic replay in both interpreter modes\n'
