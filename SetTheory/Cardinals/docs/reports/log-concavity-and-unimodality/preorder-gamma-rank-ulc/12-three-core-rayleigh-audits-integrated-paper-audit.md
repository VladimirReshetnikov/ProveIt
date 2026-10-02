# Integrated paper mathematical audit

Date: October 1, 2026. Verdict: **APPROVED**.

The six-page manuscript faithfully integrates the approved computer-assisted
boundary theorem, its ordinary full core-Rayleigh and negative-correlation
corollaries, and the exact four-core coefficient obstruction. This review
covered the complete TeX, the rendered PDF's extracted mathematical text,
source snapshots, original approval receipts, exact finite counts, the added
degree-drop argument, and the background citation.

## Previously approved results

The all-size localization is complete: every potentially negative boundary
monomial has three or four exterior vertices with the stated multiplicities.
The 12 four-exterior types and 36 three-exterior types give 11,392 and 5,984
graphs, respectively. The total 48 types, 17,376 graphs, and 228,264 independent
support instances match the exact receipts. Independent variable multiplicities,
ordered factors, and Boolean support feasibility remain correctly distinguished
from matching-witness counts.

The fresh-private-head argument extracts the middle Rayleigh coefficient
formally and does not require division by a positive numerical activity.
All zero-weight boundaries are valid. The covariance calculation uses a
positive normalizer for positive core monomers and applies to the endpoint-
support probability measure, not to matching witnesses. The text correctly
limits the result to nonnegative core monomers and does not infer real
stability or Rayleigh inequalities in other variables.

The four-core graph, its 2+3 role cover, all four Boolean support polynomials,
the coefficient `−1`, and the exact rational two-square identity agree with
the approved independent reconstruction. The displayed degree-four matching
is valid. The manuscript clearly treats the example as a coefficientwise
obstruction, not a scalar-Rayleigh, real-rootedness, or ULC counterexample.

## Newly audited actual-degree argument

Section 4 adds a self-contained argument for the actual-degree-two inequality
`A²≥4B`. It is correct, including zero activities and opposite arcs:

1. Put one vertex in a compatibility graph for each positive-weight directed
   arc, and join two vertices when the corresponding arcs are physically
   disjoint. Their vertex weights sum to `A`, since every one-edge support
   corresponds to exactly one directed arc
2. If the actual support degree is at most two, this graph is triangle-free.
   A triangle would be three pairwise physically disjoint positive-weight
   arcs and hence a positive-weight size-three support
3. Its weighted edge sum counts size-two matching witnesses. Every feasible
   positive-weight endpoint support contributes at least one witness with
   exactly that support's weight, so this edge sum dominates `B`
4. For two nonadjacent positive-weight vertices with neighbor-weight sums
   `N_p≥N_q`, moving all weight at `q` to `p` changes the edge sum by
   `w_q(N_p−N_q)≥0` and preserves total mass. No edge joins `p,q`, so these
   neighbor sums are independent of their two weights. Each move reduces the
   number of positive-weight vertices. Eventually they form a clique, of size
   at most two by triangle-freeness. Its edge sum is at most `A²/4`

The argument is valid for an empty or one-vertex positive-weight support as
well. It is an abstract weighted graph inequality; intermediate redistributed
weights need not themselves arise as products of role activities.

The first cubic inequality follows from `b_ij≤a_i a_j` and
`A²≥3Σ_(i<j)a_i a_j`. The second is the approved three-square identity. Thus
the manuscript's actual-degree rank-ULC conclusion is justified for degrees
three, two, one, and zero. The sum-of-squares consequence is scalar, not a
claim of coefficientwise nonnegativity of the full Newton difference.

## Source and artifact checks

All three proof-note snapshots match the hashes in their original approvals.
Both independent checker copies are byte-identical to the audited originals.
The background reference was checked at its primary arXiv record: David G.
Wagner, *Rank three matroids are Rayleigh*, submitted March 12, 2004,
https://arxiv.org/abs/math/0403216. It is explicitly contextual rather than a
premise of the directed-support proof.

Approved final content hashes:

- TeX: `47786046a01df16295bc37ebd29720fe56a32637134aeb5a552b5a4bbec6dba1`
- PDF: `532a215320160a20c6b0afa8df20c050d76ed537d2b7ce958e1d719895654ce7`

The producer records visual page inspection separately. Fresh-archive replay
will be recorded outside the frozen package after assembly. This approval
does not claim a second independent visual inspection or a proof-assistant
formalization. Earlier delivered artifacts were not modified.
