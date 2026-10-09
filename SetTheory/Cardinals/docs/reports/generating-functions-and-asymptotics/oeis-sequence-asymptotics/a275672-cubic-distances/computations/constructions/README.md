# Certified constructive lower bounds for unique-distance cubic grids

This package contains integer-coordinate witnesses for every n=7,...,30.
Each witness proves a lower bound on a_n. This constructive package does not
claim maximality; the companion research article and exact-search artifacts
provide any upper-bound or exact-value claims.

All coordinates use 0,...,n-1. Add 1 to every coordinate to recover the convention
1,...,n in the problem statement. Translation leaves every distance unchanged.

## Verified table

|n|Certified lower bound|Distinct unordered-pair distances|
|---:|---:|---:|
|7|10|45|
|8|12|66|
|9|13|78|
|10|14|91|
|11|15|105|
|12|16|120|
|13|17|136|
|14|18|153|
|15|18|153|
|16|18|153|
|17|19|171|
|18|20|190|
|19|21|210|
|20|22|231|
|21|22|231|
|22|23|253|
|23|24|276|
|24|25|300|
|25|26|325|
|26|26|325|
|27|27|351|
|28|28|378|
|29|29|406|
|30|30|435|

`data/witnesses.json` contains every coordinate, every squared distance, and a
mapping from each distance to its unique unordered pair of point indices.
The original n8/n9/n10 witnesses used in the article are preserved separately
in `data/original_witnesses` and `data/main_witnesses.json`, even if another
search later improves a bound or finds a different witness of equal size.

## Verification

Run `python3 scripts/verify_bundle.py` or `make verify`.
The verifier uses only Python integer arithmetic and the standard library.
It checks cube membership, distinct points, positivity, all unordered pairs,
and equality of the recomputed distance inventory with the stored inventory.
No floating-point comparisons or geometric tolerances are used.

## Deterministic reproduction

Run `make` with a C++17 compiler, then:

```
python3 scripts/reproduce.py --n 10
python3 scripts/reproduce.py --n 9
python3 scripts/reproduce.py --n 8
```

The n10 command reproduces the original 14-point witness; n9 reproduces 13
points and n8 reproduces 12. The immutable starting certificates are in
`data/starting_points`. Seeds and exact iteration caps are in
`data/reproduction_manifest.json`. A negative budget argument is an iteration
cap; a positive budget is elapsed seconds. The random engine is
`std::mt19937_64`; exact point-for-point reproduction was checked with the
GCC/libstdc++ environment used for this package. Different standard-library
implementations of `std::shuffle` need not generate identical trajectories.
Witness validity is independent of reproducibility of the search trajectory.

Example direct call:

```
bin/feasible_walk 10 13 101314 -5858 data/starting_points/original_n10.json result.json
```

## Algorithms and interpretation

`adaptive.cpp` replaces one point at a time, evaluates the exact collision
count using cached point-to-grid distances, and uses tabu memory, weighted
distance penalties, and randomized restarts. `spread.cpp` also sometimes
breaks ties by the sum of squared distances from the candidate to retained
points. These are heuristics; a nonzero best collision count is not an upper
bound.

`feasible_walk.cpp` maintains a valid k-point set. It deletes 3 points, or 4
with probability 1/3, enumerates points individually admissible against the
fixed core, shuffles them, and recursively fills the vacant places. Every
new edge is tested against all used distances. A refill of r+1 points
certifies a valid (k+1)-point set. Otherwise a reservoir sample of valid
r-point refills becomes the next k-point state. A move is capped at 200,000
recursive nodes; this cap and the randomized walk make unsuccessful searches
inconclusive. Its safe per-move cost is O(n^3 k + B C k), where C<=n^3 is the
candidate count and B<=200,001 is the recursive-node cap. Memory is
O(n^3+n^2+k^2). The optional forbidden-distance parameter restricts the search
and should be used only as an explicit auxiliary condition.

`complete.cpp` exhausts deletion-and-refill neighborhoods of one supplied
configuration. Exhausting such a neighborhood does not exhaust all subsets
of the grid. `extract.py` finds a largest valid subset of one supplied
approximate configuration by solving its small forbidden-set hitting problem;
it does not optimize over the whole grid.

`deep_walk.cpp` uses the same feasible-set algorithm but deletes 4 or 5 points
per move. This larger neighborhood found the 16-point n12 and 18-point n14
certificates after the first deletion 3/4 attempts did not find them.

Repeated lower bounds in the table do not imply repeated exact terms or
disprove strict monotonicity. A feasible-walk output with `success: false`
is still a valid k-point certificate; it means only that the attempted
increase to k+1 was not found.

All elapsed times describe particular warm-started runs on shared hardware.
They are not a controlled comparison between algorithms. The verified point
sets are mathematical certificates regardless of how the search found them.

## Figure

`figures/witness_n8.pdf` (also PNG/SVG) displays the original 12-point witness
and its exact squared-distance spectrum: 66 used values and 21 other values
that are possible in the 8^3 grid. `scripts/plot_witness.py` regenerates the
figure with matplotlib and NumPy; these packages are unnecessary for verifying
the mathematical certificates.
