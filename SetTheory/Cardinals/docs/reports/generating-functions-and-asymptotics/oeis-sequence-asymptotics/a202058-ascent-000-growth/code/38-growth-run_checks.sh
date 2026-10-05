#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
N="${1:-176}"
if [[ ! "$N" =~ ^[1-9][0-9]{0,2}$ ]] || (( N > 395 )); then
  echo "Expected an integer maximum between 1 and 395" >&2
  exit 2
fi
mkdir -p checks/build
g++ -O3 -std=c++17 checks/compute_exact.cpp -lgmpxx -lgmp -o checks/build/compute_exact
checks/build/compute_exact "$N" > checks/build/rebuilt.txt
python3 checks/verify.py --rebuilt checks/build/rebuilt.txt --expected-max "$N"
echo 'Verifier regression tests: normal Python'
python3 checks/test_verify.py
echo 'Verifier regression tests: optimized Python (-O)'
python3 -O checks/test_verify.py
