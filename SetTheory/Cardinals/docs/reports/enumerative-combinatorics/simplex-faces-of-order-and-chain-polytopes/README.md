# Largest Simplex Faces under Ordinal Sums

Research draft prepared for Vladimir Reshetnikov, 20 September 2026.

## Read the article

`Largest_Simplex_Faces.pdf` is the 20-page article. Its complete LaTeX source,
including bibliography and numerical tables, is `Largest_Simplex_Faces.tex`.

The chosen problem is explicitly posed in the concluding paragraph of:
Ragnar Freij-Hollanti and Teemu Lundström, *Simplex Inequalities of Order and
Chain Polytopes of Recursively Defined Posets*, Order 43, article 31 (2026),
published 2 September 2026, DOI: 10.1007/s11083-026-09744-1.

## Main results in the draft

For a finite poset P, let s_O(P) and s_C(P) be the largest dimensions of
simplex **faces** of its order and chain polytopes. Full polytopes and the
empty face count as faces. An arbitrary simplex inside a polytope does not
necessarily count.

1. Exact constant-state recurrences compute both quantities on any
   series-parallel decomposition. The order calculation remembers whether
   each endpoint is present; its normalized matrices have eight types.
2. For P = A[a1] < ... < A[ar], an ordinal sum of antichains,
   s_O = r + nu and s_C = r + max(0, k-1). Here k counts nonsingleton layers
   and nu is a maximum cardinality b-matching of the layer path with
   capacities min(ai-1, 2). The article gives a nonrecursive conflict-path
   formula for nu and a complete proof.
3. For n >= 2, the maximum of s_C(P)-s_O(P) over all n-element
   series-parallel posets is exactly floor((n-2)/3). Explicit extremizers
   alternate two-element antichains and singleton layers.

The scope is **finite series-parallel posets**. The draft does not claim
an efficient formula for arbitrary indecomposable finite posets, a result
about infinite ordinals, or a solution to the unrestricted Hibi–Li
face-number conjecture. The known inequality s_O <= s_C in this class is
not claimed as new. The contribution is the exact evaluation, closed
layer formula, and sharp extremal discrepancy.

This is an AI-assisted research draft, not a peer-reviewed paper or a
formal proof-assistant certification. The proofs and exact computations
are provided for inspection. Novelty has not been independently verified.

## Reproduce the computations

Python 3.10 or later; standard library only. No network, solver, or extra
Python package is needed.

    python verify.py --full --output reproduced_results

A smaller smoke test is:

    python verify.py --quick --output quick_results

Run without Python's `-O` flag: verification checks use assertions.
The script deliberately writes to the named output directory; existing
files with the three output JSON names are replaced there.

The included completed run used Python 3.13.5. All checks passed:

- 5,231 naturally labelled posets through size 6 were generated, including
  1,977 series-parallel instances. Every finite poset has a natural
  labelling, so this covers every series-parallel isomorphism type through
  size 6, with some types represented more than once.
- For those SP instances, 933,762 pair-face tests and 10,456 feasible-state
  simplex-face certificates were computed from the defining inequalities.
- 30 additional seeded SP examples on 7, 8, and 9 elements passed exact
  geometric verification, with 562,028 additional pair-face tests.
- All 29,523 words over layer types {1,2,3} of lengths 1 through 9 agree
  with the closed layer formula.
- Complete signature saturation through n=15 verifies the eight states,
  the strengthened potential invariant, and the sharp gap bound.
  Signatures are not counts of nonisomorphic posets.
- All 64 state transitions and 64 potential inequalities pass.
- Extremizers are checked for every n from 2 through 100.
- The clique optimizer agrees with exhaustive subset enumeration on 250
  seeded small-graph constrained problems.
- Iterative evaluation passes a 5,000-element chain test.

The recorded full run took about 4.1 seconds in this environment; timing
is not a cross-machine guarantee.

## Use the formula evaluator

    from simplex_posets import evaluate, layered_expr, layered_formula

    P = layered_expr([2, 1, 2])
    result = evaluate(P)
    print(result.order_simplex)  # 3
    print(result.chain_simplex)  # 4
    print(result.matrix)         # (3, 3, 3, 3)
    print(result.state)          # 8

    # Return value: (s_O, s_C, matching_number).
    assert layered_formula([2, 3, 2, 1, 2, 2, 3]) == (10, 12, 3)

General expressions are `'x'`, `('S', left, right)`, and
`('P', left, right)`. The two operations mean ordinal sum and disjoint
union. Matrix entries are (m00, m01, m10, m11) in row-major order.

`evaluate` is iterative postorder and does not use recursive tuple
hashing. Its input is an expanded expression tree, not a compressed-DAG
representation with exponentially many implied elements. `decompose`
recognizes finite SP posets given their full strict transitive relations.
The auxiliary generator and geometry checker are intended for small
instances and use exhaustive, potentially exponential algorithms.

## Independent geometric checks

The geometry checker does not use the SP recurrence to compute answers.
It enumerates all filter or antichain vertices, determines edges by
intersecting their common tight defining inequalities, and solves the
resulting maximum-clique problem with endpoint constraints. Each maximum
clique is then independently checked to be a face with no extra vertices
and to have the expected exact rational affine rank.

Any simplex face gives a clique, which establishes the optimization upper
bound. Certifying a maximizing clique as a simplex face establishes
attainment. The implementation therefore need not assume the published
theorem that all cliques in these particular polytope graphs are simplex
faces.

## Included certificates

- `results/verification.json`: ranges, counts, environment, and completion.
- `results/transitions.json`: all 64 transitions and potential slacks.
- `results/examples.json`: maximizing vertex sets and active inequalities
  for six selected layered posets, including the five-element extremizer.
- `verification.log`: output from the actual successful full run.

Certificate elements are zero-indexed. Inequalities are stored as a
coefficient vector `a` and scalar `rhs`, meaning a.x <= rhs. Vertices are
lists of their coordinates equal to 1. Impossible values are serialized
as `"-infinity"`; an actual empty simplex has dimension -1 and its own
marker.

## Rebuild the PDF

A conventional LaTeX distribution with pdflatex, Latin Modern, AMS
packages, hyperref, cleveref, microtype, listings, and TikZ is sufficient.

    make pdf

Or run pdflatex on `Largest_Simplex_Faces.tex` three times. No separate
bibliography program is required. Fonts are referenced through ordinary
LaTeX packages; no font files are distributed.
