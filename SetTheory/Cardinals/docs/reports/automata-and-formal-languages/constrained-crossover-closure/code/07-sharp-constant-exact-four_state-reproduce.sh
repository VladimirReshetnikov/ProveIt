#!/bin/sh
# Complete independent pruned census, optional second complete producer run.
set -eu
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
g++ -O3 -std=c++17 -Wall -Wextra audit_four.cpp -o audit_four
g++ -O3 -std=c++17 four_state_prune_budget.cpp -o candidate_generator
./candidate_generator > regenerated-prune-budget.txt 2> four-state-high-transient-pairs.txt
./audit_four > independent-pruned-census.log
cmp independent-high-transient-pairs.txt four-state-high-transient-pairs.txt
if [ "${1:-}" = "--both" ]; then
  g++ -O3 -std=c++17 census_four_pruned.cpp -o producer_four
  ./producer_four > four-state-pruned-census.log
fi
python3 audit_families.py
python3 check_literal_four.py
python3 validate_receipts.py
