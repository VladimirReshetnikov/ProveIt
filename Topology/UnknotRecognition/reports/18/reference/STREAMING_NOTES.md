# Degree-streamed exact twist-macro homology

## Scope, provenance, and interfaces

This additive backend implements the question explicitly called **Degree-streamed
rank computation** in `reports/11/article/article.tex`, section *Prioritized
further research questions*, at repository revision
`ea2abcb115aaa58f0b193ce1e045c2def983e1e6`. That report already proposes generating
one adjacent degree pair at a time, discarding its rank-computation storage, and
accounting for the state generator and map caches. The present work answers that
engineering question. The identity

\[
\dim H_h=\dim C_h-\operatorname{rank}d_{h-1}-\operatorname{rank}d_h
\]

and its use in streamed linear algebra are established background, not a new
unknot-detection theorem. The same reduced twist-macro complex over F2 is used,
with quantum grading forgotten, as in the pinned `fastunknot.twist.core`.

The relevant files in this continuation package are:

* `fast/fastunknot/twist/streaming.py`: additive implementation; no default dispatch changes.
* `fast/tests/test_twist_streaming.py`: 17 new tests, including exhaustive independent cubes.
* `tools/benchmark_streaming.py`: paired measurements with an identical A/A control.
* `results/streaming_benchmarks.json`: all measured repetitions and outputs.
* `results/streaming_validation.log` and `results/streaming_benchmark.log`: recorded execution logs.
* This note.

Example:

```python
from fastunknot.twist import Run
from fastunknot.twist.streaming import StreamBudget, homology, recognize

full = homology(3, [Run(1, 2), Run(2, -2)], check_d2=True)
decision = recognize(2, [Run(1, 10001)])
assert decision["status"] == "KNOTTED"
assert decision["homology"]["reduced_rank"] is None
assert decision["homology"]["reduced_rank_lower_bound"] == 2

# A narrow live-storage cap may coexist with a large total computation.
full = homology(2, [Run(1, 1001)], budget=StreamBudget(
    max_live_states=2, max_layer_basis=2,
    max_live_matrix_bits=5, max_live_columns=5))
assert full["reduced_rank"] == 1001
```

`homology` always computes the full answer or raises `ResourceLimit`.
`recognize` requires one component, catches `ResourceLimit`/`MemoryError` as
`UNKNOWN`, and by default allows a rigorous early `KNOTTED` decision. Pass
`early_exit=False` to demand full homology in recognition mode.

## Graded enumeration without Cartesian-product rescans

Let the supplied signed runs have nonzero exponents with absolute values
\(m_1,\ldots,m_t\), on \(b\) strands. Write

\[
n=\sum_jm_j,\qquad \nu=\sum_{e_j<0}m_j,\qquad
S=\prod_j(m_j+1),\qquad V=(t+1)b.
\]

The original macro state is \(k_j\in[0,m_j]\). Replace its coordinate by

\[
a_j=\begin{cases}k_j&e_j>0,\\m_j-k_j&e_j<0.\end{cases}
\]

Then every differential edge increments exactly one \(a_j\), and

\[
h=\sum_j a_j-\nu.
\]

In particular negative runs must use `a=m-k`, not `a=k`. Their support bit is
present when `a != m`; positive-run support is present when `a != 0`.

For a fixed total \(s=h+\nu\), the generator enumerates the bounded
compositions \(\sum a_j=s\). If the remaining total at coordinate \(j\) is
\(R\), and \(M_{j+1}=\sum_{i>j}m_i\), it visits only

\[
\max(0,R-M_{j+1})\le a_j\le\min(m_j,R).
\]

Every visited prefix extends to a complete state: each integer between zero
and a sum of interval capacities is realizable by the remaining coordinates.
Conversely every valid state satisfies every displayed bound, so it is visited
once. There are at most \(s_h\) feasible prefixes at any fixed depth, where
\(s_h\) is the number of degree-\(h\) macro states. Thus this iterative DFS
uses \(O(t s_h+t)\) operations for that layer and \(O(t)\) working integers.
It does not scan all \(S\) tuples for each degree. Summing over degrees costs
\(O(tS+t(n+1))=O(tS)\) for nonempty run lists, since \(n+1\le S\).
The empty list is handled directly. No Python recursion-depth assumption is
needed.

The basis order inside a degree can differ from the original product order
when negative exponents occur. The matrices are related by degree-wise basis
permutations, not necessarily identical arrays. Full degree dimensions, ranks,
and homology agree; elimination XOR counts can differ with the pivot order.

## Local algebra and bounded caches

Circle geometry is still computed by the pinned core's union-find construction.
The geometry LRU has both an entry limit and a total vertex-occurrence limit.
No set of every support ever visited is retained. Consequently `geometry_builds`
counts actual constructions, including recomputations after eviction; it is
not a claim about the number of distinct supports.

The new map representation stores **circle indexes**, not a table with one
entry for each of the \(2^{c-1}\) reduced circle labelings:

* A merge stores the target-circle index of each source circle. Two X labels
  sent to one circle give zero; otherwise labels are relabeled and multiplied.
* A split stores its source circle, its two target circles, and the unaffected
  circle relabeling. It uses `Delta(1)=1 tensor X + X tensor 1` and
  `Delta(X)=X tensor X`.
* A dot map stores its two affected circle indexes. Coincident circles cancel
  in characteristic two; multiplication by X on the marked X-circle is zero.

These descriptions evaluate exactly the original `_saddle_map` and `_dot_map`
columns. The tests compare every label of every relevant map on several signed
braid contexts and exercise all four internal kinds (zero, dot, merge, split).
Circle zero remains marked throughout.

The map LRU has independent entry and integer-slot caps. A descriptor has four
scalar fields plus at most \(V\) relabeling entries. All these stored entries
are circle indexes of \(O(\log(V+1))\) bits; the cache does not store huge
one-hot masks. At one source state, a temporary list of at most \(t\) outgoing
nonzero descriptors and target offsets is retained so that each individual
matrix column can be generated without recompiling every edge. That list has
its own slot cap. A zero cache capacity disables caching; correctness is
unchanged, while repeated geometry/map compilation can increase runtime.

## Streaming invariant and correctness

Put

\[
d_h=\dim C_h,\quad r_h=\operatorname{rank}(\partial_h:C_h\to C_{h+1}),\quad
D=\sum_h d_h.
\]

The code uses `dimension` for the chain dimension and `rank` for the boundary rank.

At the start of a degree step, only the degree-\(h\) state index is retained,
together with the previous scalar boundary rank. Build the degree-\(h+1\)
index, consisting of state tuple, support mask, basis offset, and basis
dimension. The source index and target index suffice to enumerate all outgoing
edges and to assemble one column at a time. Integer-bitset elimination retains
only pivot columns. Once \(r_h\) is known, the displayed homology identity
finalizes degree \(h\); the source index is eagerly cleared and released.

Inductively, each state is enumerated once in its unique degree, every original
local edge is emitted in the correct degree and basis offset, and its compact
map equals the original Frobenius map. Thus each streamed matrix is the same
linear map as the original, up to the noted basis permutation. Gaussian
elimination returns its exact rank. The finalized degree dimensions and total
reduced rank therefore agree exactly with `twist.core.homology`.

With `check_d2=True`, each generated matrix is also recorded. Once its rank has
been computed, it is composed with the preceding recorded matrix column by
column. The preceding matrix is then cleared. This requires only **two state
indexes**, even in checking mode: the older matrix's source state index is no
longer needed. At most two adjacent matrices are retained. This is stronger
than the three-layer state-index allowance in the initial implementation brief.

## Space theorem with all retained data included

Define

\[
L=\max_h(s_h+s_{h+1}),\qquad
B=\max_h(r_h+4)d_{h+1}.
\]

Use the convention that missing end layers have dimension and state count zero.
Let \(C_g\) be the actual peak number of cached geometry vertex occurrences;
let \(C_m\) and \(A_m\) be the actual peak cached and active map descriptor
slots. On a word model large enough to hold input coordinates, support masks,
offsets and counts, the live storage of full homology without d-squared checking
is bounded by

\[
O\!\left((t+1)L+(n+1)+C_g+C_m+A_m+V+t
  +\max_h(r_h+4)\left(1+\left\lceil d_{h+1}/w\right\rceil\right)\right)
\]

machine words, where \(w\) is the bitset limb/word size. Equivalently the
algebraic bit payload is bounded by \(B\), up to the explicitly counted
integer-object and dictionary overhead. The four temporary vectors cover the
yielded generator column, an evolving reduced column, a shifted unit vector,
and an allocated XOR result; many of these are absent or aliases in practice.

This formula includes:

1. Both adjacent state indexes, with their length-\(t\) tuple keys.
2. The requested full result dictionaries, which contain \(O(n+1)\) scalar
   entries even when each chain layer is tiny.
3. Bounded geometry and map caches, active edge descriptors, and transient
   topology/descriptor construction.
4. Pivot dictionaries and bitsets, plus conservative transient vectors.

If coordinates/counts exceed one machine word, replace their word counts by
their encoded bit lengths. A safe state-index bit bound is
\(O(L[t\log(n+2)+t+\log(D+1)])\); each cached geometry/map circle index costs
\(O(\log(V+1))\) bits, and each map-cache support key costs \(O(t)\) bits.
There is no assumption that a very large binary-encoded exponent is a unit-size
integer in a bit-complexity claim.

With d-squared checking the algebraic bit envelope is at most

\[
\max_h\left\{
 d_{h-1}d_h+d_hd_{h+1}
 +\max\big((r_h+4)d_{h+1},\;4d_h+3d_{h+1}\big)
\right\}.
\]

The first two terms are adjacent recorded matrices. The final maximum covers
the separate elimination and composition phases, respectively; pivots are
released before composition. Recorded column-reference counts are bounded
separately, so an enormous list of zero columns does not escape accounting
merely because its bit payload is zero.

The original backend retains all state indexes and all matrices, whose dense
bit upper bound is

\[
Q=\sum_h d_hd_{h+1}.
\]

The new algebra term uses a maximum of adjacent-layer costs, with pivots alone
in the ordinary mode. Neither this bound nor the measured allocation savings
implies a constant-space full-output algorithm. For a single long two-strand
run, the state index and rank workspace are bounded, but the requested full
degree dictionaries still require linear output storage.

## Runtime accounting and its limits

Let \(G\) be actual geometry constructions, \(M\) actual compact-map
compilations, and \(E_h\) emitted local differential terms in degree \(h\).
All are counted. Bounded caching gives the safe bounds

\[
G\le(t+2)S,\qquad M\le tS,\qquad E_h\le2td_h.
\]

State generation costs \(O(tS)\); constructing all length-\(t\) neighboring
tuple keys costs at most \(O(t^2S)\). If one geometry construction costs
\(T_G(V)\), topology costs \(O(GT_G(V))\). The pinned core's implementation
has the elementary safe bound \(T_G(V)=O(V^2)\); no unproved inverse-Ackermann
claim is made for its particular unranked union-find code. A map compilation
needs \(O(V)\) index operations. A deliberately loose label-evaluation bound
is \(O(V(1+\lceil V/w\rceil))\) per nonzero local-map application.

Column assembly and elimination contribute at most

\[
O\!\left(\sum_h [E_h+d_h(r_h+1)]
               (1+\lceil d_{h+1}/w\rceil)\right)
\]

word operations, in addition to the local label-evaluation work. Each pivot
XOR strictly lowers the leading bit, so one column uses at most \(r_h\)
pivot XORs. Replacing \(r_h\) by \(\min(d_h,d_{h+1})\) gives a dimensions-only
bound. Optional d-squared checking adds the cost of iterating over the
nonzero entries of each recorded matrix and XORing the corresponding columns
of its successor, including the bit traversal cost. The shared XOR counter
and deadline cover those operations too.

The arithmetic rank problem has not disappeared. Large middle layers can
still require quadratic pivot storage and cubic-style elimination. Bounded
caches can also repeat work. The measured implementation trades more CPU time
for less peak storage in full-homology mode. It establishes no unrestricted
quasi-polynomial bound and does not implement Lackenby's hierarchy algorithm.

## Budget semantics and safe refusal

`max_states` bounds the full macro product before enumeration; this remains
distinct from `max_live_states`, which bounds the currently retained indexes.
`max_basis` bounds the total basis enumerated so far; `max_layer_basis` bounds
one degree. Full-output dictionary size is already bounded because the degree
span is at most `max_states` after the product guard. Early decision may visit
only a prefix, but it still obeys the full-product preflight bound.

`max_live_matrix_bits` is a conservative live bit-payload envelope, not the
sum \(Q\) over all degrees. `max_live_columns` separately bounds matrix and
pivot reference counts, with temporary-vector allowance. Geometry and map
caches have independent caps; `max_active_map_slots` controls the per-source
temporary edge descriptors. A construction in flight can temporarily sit
outside its cache, so the reported bounds include two further geometry grids
and two further maximal compact descriptors. `max_grid_vertices` bounds each
topology construction before allocation.

Default cache limits are 128 geometries, at most 1,000,000 cached geometry
vertex occurrences; 1,024 maps, at most 100,000 cached map integer slots; and
1,000,000 active map slots. These limits do not grow with the number of degrees.
The final stats report both actual peaks and the conservative combined bounds.

The macro product is checked by division before each multiplication. An
exponent of more than 20,000 bits is rejected under a small state cap without
converting it to decimal. Huge strand counts are rejected by the grid guard
before grid allocation. The shift producing a single state's exponentially
large basis dimension is guarded using a bit-length comparison. All these
failure modes remain `UNKNOWN` in recognition mode.

As in the pinned backend, these are algorithmic storage units and cooperative
deadlines, not an operating-system RSS reservation or hard real-time timeout.
Python object headers, allocator arenas, and integer temporaries have overhead.
The recorded `tracemalloc` experiment measures that implementation overhead
separately; it does not redefine the mathematical caps as byte guarantees.

## Exact early decision

After degree \(h\) is finalized, let

\[
R_{\le h}=\sum_{i\le h}(d_i-r_{i-1}-r_i).
\]

Every summand is an actual nonnegative homology dimension, so this is a lower
bound on the full reduced rank. For a one-component input, once it exceeds one,
the same rank-one unknot-detection theorem used by the pinned backend certifies
`KNOTTED`; later homological degrees cannot cancel already computed homology.
This differs from summing chain dimensions or using an unfinished rank estimate.

An early result returns `reduced_rank=None`, the lower bound, the finalized
nonzero degrees, and `homology_complete=False`. Its chain dimensions may include
one additional assembled target degree. With checking enabled,
`d_squared_checked_through_degree` identifies the verified prefix, while the
full-complex flag `d_squared_checked` remains false. `UNKNOT` is returned only
after the full reduced rank has actually been computed as one.

For a positive two-strand run of odd length at least three, the first four
macro states suffice to finalize degree 0 with dimension one and degree 2
with dimension one. The negative version needs three states. The early method
therefore avoids computing the remaining long tail on this family, although
these knots are already easy for existing inexpensive recognition filters.
The benchmark is explicitly a raw-backend experiment, not a claimed gain over
the repository's determinant-first recognition pipeline.

## Validation and reproducibility

Run:

```sh
PYTHONPATH=fast python -m unittest discover -s fast/tests -p 'test_twist*.py' -v
python tools/benchmark_streaming.py --output results/streaming_benchmarks.json --rounds 7 --batch 5
```

The recorded suite has **92 passing twist-related tests**, including **17 new
tests**. The new suite compares **468 exhaustively enumerated signed braid
words** against the independently assembled ordinary crossing cube: all
two-strand words of length at most six (127), and all three-strand words of
length at most four (341). Empty words, links, equivalent braids and repeated
knot types are included; these are not 468 distinct knots. Six additional
actual signed braid closures, including the repository's 11-crossing Morton
case, are also compared with the independent cube. All comparisons use
homological degree counts, and both implementations verify d-squared.

Further checks compare full chain dimensions and boundary ranks with the
pinned macro backend; compare all compact map kinds with its label tables;
exercise positive and negative gradings; disable or sharply cap both caches;
test resource refusal and exact early-decision flags; and check the exact peak
adjacent-state count. These are finite implementation checks. General
correctness rests on the unchanged macro-complex mathematics and the storage/
enumeration argument above, not on the test corpus alone.

The eight benchmark cases include long single runs, mixed signed runs, an
uncancelled conjugated unknot, a mixed four-strand context, the weaving word
`[1,-2]*4`, and the **existing** `benchmark_twist.py` Morton word
`[-3,-3,2,-3,2,1,1,1,-2,1,-2]`. Every full-output arm agrees on reduced rank,
every homological degree, every chain dimension, and every boundary rank.
The original and an identical original-backend control are independently
rerun. Randomized arm order uses seed 2026100801. Each of seven rounds averages
five fresh repetitions per arm; validation is outside each recorded duration,
and raw individual durations are preserved. D-squared is checked before the
timed rounds, not inside them. No braid simplification or earlier invariant
filter is timed.

Memory tracing is performed in separate fresh computations after the timed
rounds. Reported peaks are newly traced Python allocations from `tracemalloc`,
not total process RSS. Raw data, full results, budget values, Python/platform
metadata and the benchmark scope are in the JSON. Timings in this shared
environment vary; A/A ratios reveal the remaining noise. The full streamed
backend is slower on these cases, while its allocation peaks are smaller.

The Morton input supplies a concrete full-profile audit. Its degrees -5 through
6 have chain dimensions

\[
(8,48,138,270,417,518,510,414,278,142,48,8)
\]

and outgoing boundary ranks

\[
(8,40,98,172,245,272,238,176,102,40,8,0).
\]

Thus only degree zero has homology, of dimension one. There are 768 macro
states, 2,799 total basis vectors, and at most 308 simultaneously retained
state-index entries. The full matrix sum is \(Q=1,009,952\) bits. The ordinary
streamed run records no whole matrix; it reaches 272 pivots and retains only
the two current state layers. The exact live-bit envelope and cache/allocation
peaks for the final implementation are recorded in the JSON, so they can be
checked independently of rounded article tables.

## Further implementation questions

1. Preserve the space guarantees while recovering full-computation speed,
   especially by reducing interpreter overhead and using bounded small-label
   table caches where their measured benefit justifies their explicit cost.
2. Use profile information to choose the direction of the degree sweep, or to
   choose a provably safe early-decision order, without holding the full state
   product in memory. Reversing the sweep requires correct transposed local
   maps and grading conventions.
3. Replace long, eventually repeated degree tails by symbolic interval data
   when a separate theorem identifies their homology. Streaming alone still
   visits each degree required in the explicit full-output interface.
4. Evaluate on filter-undecided inputs before considering a default dispatcher
   change. The present raw-backend early successes do not establish that such
   difficult inputs become fast.
5. Move the pivot bitsets and compact map evaluation into a lower-overhead
   exact kernel while retaining independent cube checks and the same resource
   semantics. Any resulting wall-time claim needs a fresh paired experiment.
