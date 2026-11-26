#!/bin/sh
# Replay from any working directory, using a temporary build directory.
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
c++ -std=c++17 -O3 "$src/cm_small.cpp" -o "$out/cm_small"
"$out/cm_small" 10000000 > "$out/raw.txt"
python3 "$src/cm_intervals.py" "$out/raw.txt" > "$out/residual.txt"
cmp "$src/cm_small_unresolved.txt" "$out/residual.txt"
