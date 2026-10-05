#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
PYTHON="${PYTHON:-python}"
mkdir -p checks
"$PYTHON" check_repair.py > checks/normal.log
"$PYTHON" -O check_repair.py > checks/optimized.log
cmp checks/normal.log checks/optimized.log
"$PYTHON" independent_check.py > checks/independent-normal.log
"$PYTHON" -O independent_check.py > checks/independent-optimized.log
cmp checks/independent-normal.log checks/independent-optimized.log
for mode in normal optimized; do
 args=()
 if [ "$mode" = optimized ]; then args=(-O); fi
 if "$PYTHON" "${args[@]}" check_repair.py --inject-error > "checks/negative-$mode.log" 2>&1; then
  echo "ERROR: deliberately corrupted coefficient was accepted ($mode)" >&2
  exit 1
 fi
 grep -q 'ValueError: Log coefficient 3' "checks/negative-$mode.log"
done
echo 'Normal and optimized verification passed with identical output.'
echo 'Independent finite-PGF recurrence and brute-force model checks passed in both modes.'
echo 'Deliberately corrupted third-order coefficients rejected in both modes.'
