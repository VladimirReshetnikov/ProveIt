Bounded local discovery using contract-derived tape windows
==========================================================

The script collects a conservative set of local bit patterns from all
4,815 symbolic source contracts and the exact startup of M195S8.
Unknown register bits and affine-run lengths are overapproximated.
Opaque register-engine and self-sweeping controls are excluded.

Two completed screens:

  left3/right1: 5 tape cells, 1,454 patterns
  left6/right2: 9 tape cells, 7,006 patterns

Each uses 165 eligible controls, 13,530 pairs and 258,720 initial actions.
Existing table controls may execute arbitrary finite local detours, with
exact cycle detection, but may not re-enter either prospective merged
control before the matching endpoint. Neither screen found a candidate.

The retained contexts.json and contexts.txt are the nine-cell run.
The five-cell run is reconstructed from the same script:

  python3 contexts.py 3 1
  g++ -O3 -std=c++17 search.cpp -o search
  ./search contexts.txt

For nine cells, use "python3 contexts.py 6 2".
Run in a research copy if preserving the delivered input hashes matters.

These are particular discovery screens. They do not exclude all larger
context transformations, multi-control edits, or context-specific source
optimizations. Any survivor would still require complete source/runtime
and startup validation; no survivor was available.
