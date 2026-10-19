#!/bin/sh
# Independent search reproduction. No repository code is imported or executed.
set -eu
: "${B245_INPUTS:?Set B245_INPUTS to the prepared mathematical input directory}"
B245_OUTPUTS=${B245_OUTPUTS:-"$(pwd)/search-output"}
export B245_OUTPUTS
mkdir -p "$B245_OUTPUTS"
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
python3 -B "$HERE/prepare_search.py"
python3 -B "$HERE/prepare_joint.py"
python3 -B "$HERE/prepare_unlocked_roots.py"
for stem in search_rotations search_rotations_relax search_joint search_joint_fast; do
 g++ -O3 -std=c++17 "$HERE/$stem.cpp" -o "$B245_OUTPUTS/$stem"
done
python3 -B "$HERE/search_grammar.py" 120 123 > "$B245_OUTPUTS/search123.log" 2>&1
"$B245_OUTPUTS/search_rotations" "$B245_OUTPUTS/search-input.txt" 300 42 "$B245_OUTPUTS/rot42.best" > "$B245_OUTPUTS/rot42.log" 2>&1
"$B245_OUTPUTS/search_rotations_relax" "$B245_OUTPUTS/search-input.txt" 240 71 "$B245_OUTPUTS/relax71.best" relax > "$B245_OUTPUTS/relax71.log" 2>&1
"$B245_OUTPUTS/search_joint" "$B245_OUTPUTS/joint-input.txt" 300 729 "$B245_OUTPUTS/joint729.best" > "$B245_OUTPUTS/joint729.log" 2>&1
"$B245_OUTPUTS/search_joint_fast" "$B245_OUTPUTS/joint-input.txt" 240 2026 "$B245_OUTPUTS/joint2026.best" relax > "$B245_OUTPUTS/joint2026.log" 2>&1
"$B245_OUTPUTS/search_joint_fast" "$B245_OUTPUTS/joint-unlocked-roots-input.txt" 180 647 "$B245_OUTPUTS/joint647.best" relax > "$B245_OUTPUTS/joint647.log" 2>&1
python3 -B "$HERE/surgical_zero5.py" > "$B245_OUTPUTS/surgical_zero5.log" 2>&1
# Optional NumPy/SciPy models. Timeouts are not infeasibility results.
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 -B "$HERE/milp_grammar.py" 40 30 > "$B245_OUTPUTS/milp40.log" 2>&1
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 -B "$HERE/milp_grammar128.py" 40 30 > "$B245_OUTPUTS/milp128.log" 2>&1
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 -B "$HERE/milp_prefix.py" 80 180 > "$B245_OUTPUTS/milp_prefix.log" 2>&1
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 -B "$HERE/milp_radius.py" 80 90 > "$B245_OUTPUTS/milp_radius.log" 2>&1
