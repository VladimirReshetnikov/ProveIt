# Exact search for the three-dimensional distinct-distance lattice problem

## Certified computation

The complete run in `n7_k11_diameters_v5.json` exhausts all 31 cube-isometry
orbits of possible diameter edges of an 11-point configuration in
`{0,...,6}^3`. Every case is UNSAT. The run visited 60,290,915 recursive
search nodes and took 525.875 seconds under shared CPU load. The separate
file `n7_k10_v5.json` gives ten points with 45 distinct squared distances.
Together these computations establish `a(7)=10`.

The complete run `n8_k13_top6_all.json` exhausts all 23 diameter orbits for
13 points in `{0,...,7}^3`. Every case is UNSAT: 38,430,195 clique-search
calls and 445.028 seconds. The independently checked twelve-point
witness `n8_k12_verified.json` contains 66 distinct squared distances.
Together these establish `a(8)=12`. The exact source of this run is
`rainbow_edge_prefix.cpp`, using mode `top6`.

The source of the original complete n=7 run is `rainbow_exact_v5.cpp`; its SHA-256 is
recorded in `MANIFEST.json`. Reproduce it with:

```sh
g++ -O3 -std=c++17 rainbow_exact_v5.cpp -o rainbow_exact_v5
./rainbow_exact_v5 7 11 1200 diameters
./rainbow_exact_v5 7 10 60
```

The positive witness can be checked without running the search: verify
the coordinate bounds, that there are ten distinct points, and that the
45 sums of squared coordinate differences are pairwise different.

The search log is a record of a reproducible exhaustive computation, not
a DRAT proof or a certificate checked by a small theorem-prover kernel.
Correctness rests on the mathematical reductions below and the supplied
implementation. Independent review and independent runs are appropriate.

## The diameter case split

Let `D={d_1<...<d_t}` be the attainable positive squared distances in the
box, and let `K=binom(m,2)`. Any m-point solution has K distinct distances,
so its largest distance is at least `d_K`. For n=7 and m=11, `K=55` and
`d_55=68`.

There are exactly 810 unordered pairs of lattice points with squared
distance at least 68. The 48 isometries obtained by permuting coordinates
and independently reflecting them about the middle of the cube divide
these pairs into 31 orbits. The solver enumerates the lexicographically
least pair in every orbit. Pair endpoints are unordered.

For each representative `(p,q)` with squared distance `R`, both endpoints
are selected. Every other selected distance must be strictly less than
`R`, because all distances are distinct and `(p,q)` is the diameter.
The initial candidates satisfy:

* `d(p,x)<R` and `d(q,x)<R`;
* `d(p,x)!=d(q,x)`.

The subsequent search allows no new edge longer than R, and the used
distance mask already contains R, so equality with R is forbidden too.

## Exact dynamic compatibility

At any search node let S be the selected points, U the set of their
pairwise squared distances, and C the remaining individually admissible
points. For each candidate x, let

`M_x={d(x,s):s in S}`.

The invariant is that U has no repeated distance, each `M_x` has exactly
`|S|` elements, and `M_x` is disjoint from U. Two candidates x,y are
compatible exactly when

1. `M_x` and `M_y` are disjoint;
2. `d(x,y)` is outside `U union M_x union M_y`;
3. `d(x,y)` is at most the current maximum permitted unprocessed distance.

These conditions account for every pair-distance collision in
`S union {x,y}`. Thus the vertices of any completion form a clique in the
compatibility graph on C.

Selecting v replaces U by `U union M_v`. For every surviving candidate x,
its radial mask becomes `M_x union {d(x,v)}`. Compatibility guarantees the
same invariant at the child node.

A greedy proper coloring of the compatibility graph provides a rigorous
upper bound for its clique number. The solver branches in reverse color
order; when the number of remaining colors is smaller than the number
of points still needed, the branch is impossible. This is a complete
branch-and-bound search, not a greedy attempt to construct one solution.

The later edge-prefix implementation also removes the `(L-1)`-core
complement when L points remain to be selected: a vertex of degree less
than L-1 cannot belong to an L-clique, and deletion can be iterated.

## Distance and parity capacity pruning

Let A be the union of:

* the used distances U;
* all radial masks `M_x`;
* the distances of compatible candidate-candidate edges.

Every distance in a completion belongs to A, so `|A|>=K` is necessary.
Also, the union of radial masks must contain at least `|S|*L` distances
when L further points are needed.

Checkerboard parity gives another necessary condition. If the final
configuration has b points of one checkerboard color and m-b of the
other, exactly `b*(m-b)` distances are odd. The solver tests the feasible
values of b against the numbers of available odd and even distances and
the numbers of candidates of each color.

The stronger modulo-four constraint uses the eight coordinate parity
classes indexed by `v in {0,1}^3`. Squared distance modulo four equals
the Hamming distance between the coordinate parity classes. For a final
occupancy vector `(N_v)` summing to m, the numbers of required distances
in each residue class are

* `R_0=sum_v binom(N_v,2)`;
* `R_r=sum_{v<w, Hamming(v,w)=r} N_v*N_w`, for r=1,2,3.

At every node each R_r must fit the available distances of that residue.
The occupancies must also lie between the already selected counts and
the selected-plus-candidate counts, class by class. All feasible
occupancies are enumerated initially, then filtered down the search
tree. In the n=7,m=11 problem there are initially 2,376 feasible vectors.

These arithmetic tests are necessary conditions only. They never assert
existence of a geometric configuration.

## Residual symmetry

After fixing a diameter edge, its setwise stabilizer still acts on the
remaining points. Let H be that stabilizer. Among all H-images of a
completion, choose one whose sorted remaining point list is
lexicographically least. If r is its first remaining point, then

* r is the least point in its H-orbit;
* no selected remaining point has an H-orbit representative less than r.

Otherwise an element of H would produce a completion with a smaller
first remaining point. This justifies branching only on such r and
discarding candidates whose orbit representative is smaller. The v5
source applies this reduction when `|H|>=4`.

The optional single-anchor mode uses the analogous reduction under
cube isometries and translations of the entire finite configuration.
The n=7 upper-bound certificate does not depend on that optional mode.

## Larger prefixes of the longest edges

The optimized sources `rainbow_top_edges.cpp` and
`rainbow_edge_prefix.cpp` use a stronger complete case split. If the
selected distances in descending order are

`b_1>b_2>...>b_K`,

then the r-th largest distance satisfies `b_r>=d_(K-r+1)`. Consequently
the second-largest edge in the n=7,m=11 problem has squared length at
least 66. For n=8,m=13 the first two thresholds are 101 and 99.

Once the first r largest edges are fixed, their endpoints are selected,
and every other selected distance is at most the last fixed length.
When extending the prefix, any already selected edge that is not yet
processed must also be no longer than the proposed next edge. The
solver checks this explicitly and recomputes all distances on the
expanded endpoint set, rejecting any collision.

The next edge is enumerated modulo the subgroup fixing each earlier
edge setwise. Its endpoints can both be new, one can be new, or both can
already be selected. All three possibilities are included. At the end
of the desired prefix, ordinary dynamic clique search completes the
configuration. This is exhaustive because every putative solution has
a unique ordered list of its largest edges.

The recursive implementation accepts modes `top2` through `top6`:

```sh
g++ -O3 -std=c++17 rainbow_edge_prefix.cpp -o rainbow_edge_prefix
./rainbow_edge_prefix 8 13 1200 top6
```

The prefix computation adds selected endpoints rapidly while excluding
large distances from all later edges. It has no claimed polynomial or
quasipolynomial worst-case bound. Its usefulness is an exact-search
improvement for the finite instances considered here.

Two additional complete runs on n=7,m=11 corroborate the one-edge
computation. The four-edge prefix run took 43.7672 seconds and 5,244,129
clique-search calls; the six-edge prefix run took 70.6526 seconds and
8,975,935 clique-search calls. Every one of the same 31 diameter cases was
exhausted in both runs. These computations share the compatibility and
clique-search kernel, so they are not independent implementations.

Prefix depth is a tuning parameter, not a monotone improvement. In this
n=7 instance, depth four outperformed depth six. In the separately
benchmarked n=8,m=13 diameter case 3, depth four needed 9,061,517 clique
calls, depth five needed 3,068,670, and depth six needed 2,088,845.
These single-case results do not by themselves establish an upper bound
for n=8.

## Scope, limits, and reproducibility

Each JSON result identifies whether its UNSAT status covers one case or
all cases. A single-case UNSAT result is not an upper bound for the full
problem unless every case has been covered. `UNKNOWN` or an interrupted
process establishes no new upper bound.

The implementations use fixed bit-mask storage appropriate for
`1<=n<=10`, and reject larger n. Coordinates are zero-based. The model
is identical to `[1,n]^3` after adding one to every coordinate.

Complete small validation runs included here reproduce a(5)=7 and
a(6)=9. The known upper bound a(6)<=9 also follows directly from the 44
attainable squared distances, because 10 points would require 45.

The compiler and hashes are recorded in `MANIFEST.json`. Wall-clock
times were obtained under varying shared CPU load and should not be
treated as a controlled machine benchmark. Search-node counts are more
stable, but different versions can define their branching nodes
differently; the edge-prefix code counts the ordinary clique-search
calls and does not add separate prefix-enumeration nodes to that field.
