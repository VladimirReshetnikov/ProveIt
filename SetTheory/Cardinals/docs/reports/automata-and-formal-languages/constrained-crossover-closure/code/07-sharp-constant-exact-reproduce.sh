#!/bin/sh
# Full independent two/three-state reruns and pointwise three-algorithm comparison.
set -eu
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
g++ -O3 -std=c++17 -Wall -Wextra audit_census.cpp -o audit_census
g++ -O3 -std=c++17 producer/census.cpp -o original_cutoff
g++ -O3 -std=c++17 producer/census_graph.cpp -o original_graph
g++ -O3 -std=c++17 -Wno-return-type compare_pointwise.cpp -o compare_pointwise
for n in 2 3; do
  if [ "$n" = 2 ]; then word=two; else word=three; fi
  ./audit_census "$n" > "independent_${word}_state.json"
  ./compare_pointwise "$n" > "pointwise_${word}_state.json"
done
./original_cutoff 3 > original_cutoff_rerun.json
./original_graph 3 > original_graph_rerun.json
python3 audit_literal.py
python3 validate_receipts.py
