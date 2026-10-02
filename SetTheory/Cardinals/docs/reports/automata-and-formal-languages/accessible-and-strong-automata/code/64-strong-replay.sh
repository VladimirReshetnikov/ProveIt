#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
PYTHON=${PYTHON:-python3}
work=.replay/work
mkdir -p "$work/independent_checks"
cp generate_coefficients.py verify_precision.py verify_exact_sectors.py verify_inverses.py verify_all_model_inverses.py verify_cyclic_lifts.py "$work/"
cp coefficients_k*.json "$work/"
cp independent_checks/*.py "$work/independent_checks/"
for k in 2 3 4; do
  (cd "$work" && "$PYTHON" generate_coefficients.py --k "$k" --order 5 --digits 70 --output "coefficients_k$k.json") > ".replay/coefficients-k$k.log"
done
for script in verify_precision verify_exact_sectors verify_inverses verify_all_model_inverses verify_cyclic_lifts; do
  (cd "$work" && "$PYTHON" "$script.py") > ".replay/$script.log"
done
for script in derive_low_orders check_small_models; do
  (cd "$work" && "$PYTHON" "independent_checks/$script.py") > ".replay/$script.log"
done
for k in 2 3 4; do
  (cd "$work" && "$PYTHON" independent_checks/verify_exact_counts.py --k "$k" --N 600 --coefficients "coefficients_k$k.json" --output "independent_checks/exact_k$k.json") > ".replay/exact-k$k.log"
done
"$PYTHON" verify_replay.py "$work" | tee .replay/comparison.log
printf 'Full replay passed. Logs: .replay\n'
