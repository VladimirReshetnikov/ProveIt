# Proof audit

The manuscript supplies human-readable proofs. No Lean or other proof-assistant
verification was performed. The tests and separate checker are implementation
validation, not substitutes for the proofs or peer review.

## New claims

**Sharp 2K+3 support.** After a spanning-tree gauge, an interval contributes a
constant plus one cyclic residue-interval indicator. Reflection folding doubles
at most 2K jump edges to at most 4K. A reflection quotient of the discrete cycle
is a path; a changing edge cannot be fixed by the reflection. Thus there are at
most 2K quotient jumps and 2K+1 generic values. At most two corrected fixed
residues add values. The scalar family with d=4K+4, W=5d and intervals
[d-j, 4d+K+j+1) attains 2K+3. Tests compare K=1,...,30 to expansion.

**Sparse correction.** Quotient by bulk equivalence first. Only at most 2h
vertices are touched. Removing their old histogram contributions and inserting
finite connected-cluster sums proves the exact formula. Every touched cluster
has an edge, so at most h new values can appear. Repeated edges and loops retain
separate payloads.

**Epoch bound.** The divisor only drops to a proper divisor; each drop at least
halves it. A first reflection can occur once. Once a reflection exists, its
residue cannot change without a divisor drop. The bound counts stored subgroup
state changes, including occasionally a redundant permutation representation
at small moduli. It is not a global bound on hierarchy cuts or resets.

**Checker soundness.** Parent-edge traversal checks the spanning forest. Local
gauge equations fix all residual maps. Divisibility plus Bezout fixes each gcd.
The checker directly counts weights on candidate endpoint cells and traverses
the sparse quotient graph, without calling the producer's profile, gcd, or DSU
algorithms. Source normalization is shared. Python exact integer arithmetic is
trusted. Malformed structures raise errors and never yield a knot verdict.

## Reused, not claimed novel

Classical cover/monodromy correspondence; gcd description of signed-affine
orbits; AHT's general polynomial weighted-orbit algorithm; Euler-characteristic
additivity; the nonnegative disc-defect/tree identity; disjoint-set connectivity.
The new contribution is the stated support, replay, and amortization package.

## Assumptions that must not disappear

The base graph is explicit. All fibres share W. Full maps have sign +1 or -1 and
act on all sheets. Interval credits are exact, not sampled. Sparse exceptions
are explicit pointwise identifications, not uncharged long intervals. Surface
interpretations require their own geometric validity and Euler-credit proof.
A histogram does not retain full attaching maps; endpoint records do. Every
input generator and every requested full-history output is charged. Native
recognizer and incoming-archive novelty comparisons remain unexecuted.

## Counterexamples included in the article

One self-attachment and one joining attachment have the same endpoint weights
but different final histograms. Fixed residues require F, not 2F. Zero weight
does not mean zero components. Repeated positive-payload loops change weights
without changing connectivity. Alternating insertions and deletions defeats any
fixed logarithmic rebuild bound. Ordered attachment configurations can remain
numerous despite a short histogram. A positive Euler characteristic without
surface and boundary conditions is not an unknot certificate.
