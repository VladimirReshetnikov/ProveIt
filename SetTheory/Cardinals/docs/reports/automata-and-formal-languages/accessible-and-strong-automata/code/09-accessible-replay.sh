#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
PYTHON=${PYTHON:-python3}
mkdir -p .replay
run() { local name=$1; shift; echo "Running $name"; "$PYTHON" "$@" > ".replay/$name.log"; }
run identity code/verify_identities.py
run symbolic code/derive_coefficients.py
run expansion code/check_expansion.py
for k in 2 3 4; do
  run "coefficients-k$k" code/generate_coefficients.py --k "$k" --order 5 --digits 60 --output "data/coefficients_k${k}_order5.json"
done
run precision code/generate_coefficients.py --k 2 --order 5 --digits 90 --output data/coefficients_k2_order5_90digits.json
run phase-precision-regressions code/verify_numerical_precision_regressions.py
run generator-validation code/validate_generated_coefficients.py
run exact-count-checks checks/verify_exact_counts.py
run third-order checks/check_third_order.py
run comparison code/compare_independent.py
run inversion code/inversion_demo.py
printf 'PASS: all exact assertions and numerical replay checks completed. Logs: .replay/\n'
