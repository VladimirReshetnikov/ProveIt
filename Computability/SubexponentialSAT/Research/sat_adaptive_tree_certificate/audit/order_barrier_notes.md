# Order-level investigation and a barrier for explicit contraction tables

Prepared as intermediate research notes for the parent task, 2026-10-26 Pacific.
Reviewed repository: ProveIt at `fa6e904d109b738154db7fe41e7f2777e6d24aee`.

## Finding

I did not derive a proved improvement of the unrestricted SAT exponent order
`n log log n / sqrt(log n)`, nor of `n / sqrt(log n)` at fixed density.
The missing structured summation/recursive factorization interfaces in the
round-1 proposals remain missing. A better matrix multiplication exponent or
an adaptive contraction tree can genuinely reduce a leading coefficient in
an exponential bound, but the explicit-table architecture still has an
order-level obstruction on symmetric feasible index allocations.

The theorem below concerns a specified representation and computation model.
It is NOT a lower bound for SAT, arbitrary tensor contraction, implicit table
representations, algebraic circuits, or the actual nonzero coefficients of
every source-generated tensor. In particular it must not be presented as
proof that a stronger SAT algorithm is impossible.

## 1. Exact boundary-table width of the complete directed graph

Let `r >= 3`. Give every ordered pair `(g,h)`, `g != h`, one independent index
set of cardinality `Q >= 2`. A group tensor can depend on its incoming and
outgoing pair indices. A contraction table for a vertex subset `B` retains
all indices crossing from `B` to its complement and sums all indices internal
to `B`. Its number of entries is

    Q ** [ 2 |B| (r - |B|) ].

A binary full-table contraction tree starts with singleton tensors and merges
disjoint subsets until the scalar contraction remains. It explicitly constructs
each represented subset's entire boundary table. Define its width as the
largest count of boundary pair indices among its tables. Then the minimum
possible width, over all trees and all permutations of the groups, is exactly

    W_r = 2 ceil(r/3) (r - ceil(r/3)).

In particular `W_r >= 4 r^2 / 9`.

### Lower bound

Start at the root subset of size `r`, and while its size exceeds `2r/3`,
descend to a child of larger size. The first visited subset `B` of size at
most `2r/3` has size `k > r/3`: its parent had size strictly above `2r/3`,
and the selected child has at least half that size. Thus

    floor(r/3) + 1 <= k <= floor(2r/3).

The minimum of `2 k(r-k)` on this integer interval is `W_r`. This can be
checked for `r = 3m`, `3m+1`, and `3m+2`; respectively it is
`4m^2`, `4m(m+1)`, and `2(m+1)(2m+1)`. Concavity of `k(r-k)` means a minimum
is attained at an interval endpoint. Therefore some explicitly constructed
table contains at least `Q ** W_r` entries.

### Matching upper bound

Partition the `r` vertices into three nonempty blocks whose sizes differ by
at most one. Contract inside each block using any binary tree. Every internal
subset has size at most `ceil(r/3)`, so its boundary has at most `W_r` indices.
Merge two of the three blocks; its boundary has the same size as the boundary
of the third block and is also at most `W_r`. Finally merge with the third
block. This constructs a tree of width `W_r`.

### Resource scope

An implementation which stores a complete boundary table necessarily stores
at least `Q ** W_r` scalar cells at some point. An implementation which emits
all entries, even if it streams them, performs at least that many output
operations. No improvement in a matrix multiplication exponent changes this
output-size statement. A specialized implicit representation, sparse table,
correlated cancellation algorithm, or direct scalar algorithm is outside its
scope. An input-specific algorithm may of course detect zeros or other special
structure and avoid the full table.

Write `h=log2(Q)` and `H=r(r-1)h`. The mandatory table exponent is

    W_r h = [W_r / (r(r-1))] H >= [4r / (9(r-1))] H.

Equal pair cardinalities make relabeling and per-allocation partition selection
irrelevant to this example. The obstruction persists even with hypothetical
matrix multiplication exponent 2.

## 2. Exact-budget feasibility: a uniform array is not merely asserted

The previous statement is about index cardinalities. To connect it to the
weighted-mode interface, use the following elementary construction.

Every ordered pair has the SAME multiset of `c` copies of each of `J` positive
integer weights `w_0,...,w_{J-1}`. Restrict all these selected mode exponents to
0 or 1. There are `2^(cJ)` subsets and their total weights lie in

    {0,...,B}, where B = c sum_{q=0}^{J-1} w_q.

Consequently at least one exact weight `b_* <= B` has at least

    Q >= 2^(cJ) / (B+1)

distinct binary mode tuples. The full nonnegative-exponent list at that exact
weight can only be larger. Because the inventories are identical, the SAME
`b_*` and SAME list cardinality can be used on every ordered pair. The array
`b_gh=b_*` is globally feasible whenever `r(r-1)B < P`, since then
`sum b_gh < P`. There is no appeal to asymptotics for an individual exact
coefficient and no assumption that every possible weight is attainable.

This is also useful if only equal-sized selected subfamilies occur in larger
pair lists: taking the identical selected subfamilies proves the stated lower
bound for each actual exact list. To make the cardinalities literally equal,
the abstract example takes the identical inventories as its complete lists.
This is a feasible inventory-level example, not a claim that every SAT input
or every actual packet construction realizes all these choices with nonzero
coefficients.

### Match to the inherited parameter scale

Fix `r >= 3`. Suppose selected Cauchy weights satisfy

    1 <= w_q <= A + 4q,

as the joint basis `w_q = A + 4q - 2 popcount(q)` does. Take

    c = Theta(M/(r^2 D)),
    J = Theta(D/sqrt(u)),
    A = o(D/sqrt(u)),

with sufficiently small fixed constants in `c` and `J` and at least `J`
available modes per family. Assume `M/(r^2 sqrt(u)) >> log(P+1)` and that
the indicated floors do not change these orders. These assumptions hold in
the usual large-packet regime for fixed `r`, but they are stated explicitly.
Then

    B = O(M D / (r^2 u)),
    cJ = Theta(M/(r^2 sqrt(u))).

The constants can be chosen so that `r(r-1) B < P` for a budget
`P = Theta(M D/u)`. The pigeonhole loss `log2(B+1)` is lower order. Hence

    log2(Q) = Omega(M/(r^2 sqrt(u))).

The boundary-width theorem gives mandatory explicit-table work/storage

    exp(Omega(M/sqrt(u))).

At the root the packing schedule has `u=O(log s)` and `M=Theta(s)`.
This architecture therefore cannot prove `exp(o(s/sqrt(log s)))` by merely
changing contraction trees, choosing partitions adaptively, or substituting
a faster matrix multiplication backend. This last sentence is about the
specified full-table architecture on the indicated admissible index
inventories; it is not an unconditional lower bound on algorithms.

If the number `r` is allowed to grow, the counting conditions and polynomial
exact-weight-array overhead must be rechecked. One must not automatically
extend the fixed-`r` theorem to an arbitrary growing schedule. In the existing
packing estimates, growth of `r` also decreases the retained taper length to
`u=O(log s/log r)`, so it does not by itself supply a free improvement.

## 3. What remains a viable order-level target

1. Construct an implicit boundary-table representation on the ACTUAL group
   functions, with closure under the required contractions and explicit entry,
   construction, precision, bit-length and memory costs. This would evade the
   explicit-table theorem. An arbitrary entry oracle alone is insufficient.
2. Prove a structured mode-sum evaluator using `exp(O(M/u))` recursive calls
   while retaining the permitted child types. This is the existing unproved
   hypothesis, not a newly solved lemma.
3. Supply a genuinely different deformation/recovery interface with precision
   or mode multiplicity below the inherited `MD/u` and `M/D` scales, or an
   operator algebra meeting the alternate manuscript's exact crossing
   interface with entropy power below 1/2.

The newest constant improvements do not close these interfaces. Finite tests
of kernels or tables cannot substitute for their required uniform proofs.

## 4. Exact source anchors

- `Computability/SubexponentialSAT/Research/3sat_precision_refinement/report.tex`,
  sections `sec:compressed` and `sec:conditional`: exact pair-index encoding,
  high-degree obstruction, and unproved structured-mode acceleration.
- The same file, proposition `prop:mode-family`: abstract binary subfamilies
  show that ordinary-degree caps do not remove square-root mode entropy.
- `Computability/SubexponentialSAT/Research/3sat_round2_refinement/research_frontier/actual_domain_rank_gate.tex`:
  actual Cauchy subblock and exact Smith valuations `4b-2 popcount(b)`; integral
  separated-basis changes cannot provide superlinear weights uniformly.
- `Computability/SubexponentialSAT/Research/3sat_precision_refinement/report.tex`,
  the exact taper minimax section: the full-loss accounting already has a
  precision-scale obstruction; retuning this taper alone does not change order.
- Incoming `subsat_contraction_tree_2026-10-26`, `report/cached_tree.tex`:
  full subset boundary tables, exact directed pair budgets, CRT matrix backend,
  and recurrence `eq:tree-recurrence`.
- Incoming `sat_adaptive_contraction_2026-10-26`, `adaptive_sat_review.tex`:
  per-weight-allocation adaptive partitions and polynomial-space separator sums.
- `Computability/SubexponentialSAT/Research/3sat_round2_refinement/research_alternate/heisenberg_entropy_barrier.md`:
  restrictions on retaining unchanged Heisenberg relations, nonlinear regrading,
  and sparse-current deletion in the alternate operator proof.

## 5. Checker

`check_table_barrier.py` independently computes the optimum peak boundary width
by dynamic programming over all possible binary split sizes, comparing it
against the closed formula for `3 <= r <= 150`. This DP covers all binary tree
shapes because boundary cost depends only on subset cardinality in the complete
uniform graph. It also enumerates exact subset-weight counts on finite Cauchy
weight inventories and checks the pigeonhole bound and a feasible uniform
exact-budget array. It checks finite consequences only; the proof is above.
