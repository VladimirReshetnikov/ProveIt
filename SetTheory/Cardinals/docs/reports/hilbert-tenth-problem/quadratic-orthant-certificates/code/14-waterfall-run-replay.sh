#!/bin/sh
# Offline exact-integer replay, using the Python standard library only.
set -eu
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
PYTHON=${PYTHON:-python3}
mkdir -p receipts
for script in verify_matrix_definition verify_frontend verify_frontend_independent grouped_quadratic verify_quadratic_independent verify_halting_example verify_certificates; do
  echo "Running $script"
  "$PYTHON" "replay/$script.py" > "receipts/$script.log"
done
"$PYTHON" replay/verify_release.py
echo 'All Waterfall replays passed.'
