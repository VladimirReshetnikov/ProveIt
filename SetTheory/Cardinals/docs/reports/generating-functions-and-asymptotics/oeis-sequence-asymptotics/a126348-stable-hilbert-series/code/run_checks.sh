#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/checks"
for script in derive_symbolic verify_symbolic_independent independent_reviewer_check verify_numeric verify_inverse verify_product verify_modular; do
  echo "Running $script"
  python -O "$script.py" > "$script.replay.log"
done
echo 'All symbolic tests and numerical diagnostics completed'
