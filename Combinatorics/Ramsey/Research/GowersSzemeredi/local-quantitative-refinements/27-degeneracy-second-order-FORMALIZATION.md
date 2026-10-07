# Proposed formalization plan

No Lean source is supplied or claimed to have compiled. This is a dependency map
for integrating the mathematical results with the existing Section 15 interface.

## Milestone 1: intrinsic relation and Boolean extraction

Keep `GeneralArrangement`, `arrangementMoment`, and
`GeneralArrangement.IsDegenerate` unchanged. Prove vanishing of every intrinsic
moment, including degenerate sides, and the Boolean zeta expansion. Boolean
inversion works in all characteristics; a prime-field first implementation fits
the current `ZMod N` interface.

Prove a minimal-degree lemma for a non-column-parity coefficient array. Record
both moments indexed by `A` and `A ∪ {lastCoordinate}`. The paired system, not
just the original single-polynomial bound, is the source of the improvement.

## Milestone 2: the first-order bound

Represent the coefficient directions modulo the intrinsic line. It is reasonable
to state the first version with explicit finite set cardinalities rather than
immediately evaluate the central-trinomial expressions.

Prove equality of zero events under `eta' = a*eta + b*intrinsic`, the hyperplane
classification, its cardinality, the elementary rank-one/rank-two estimates,
and the union bounds. Then specialize to the sharp leading coefficient.

The small-characteristic theorem requires distinguishing field size from
characteristic; composite `ZMod N` is not an extension field. Use an abstract
finite-field interface for that generalization.

## Milestone 3: second-order and cubic bounds

Prove the minimal Boolean degree split, the affine Boolean core form, the
integer width-two lemma in the stated characteristic range, and the exact core
count. Prove disjointness of parallel-slope core events on the regular region
and rank four for nonparallel slopes. The remaining directions give a cubic
error by a codimension-one cross-section constraint plus two base constraints,
or by two separate rank-two base-coordinate systems.

For characteristics 2 and 3, replace the width lemma by the finite vector-space
count of offsets and projective slope directions.

For `d=2`, compute the four-line (odd characteristic) and three-line
(characteristic two) cross-section complements. This suffices for the second
coefficient without any large certificate checker.

## Milestone 4: exact eight-vertex theorem

The Python enumeration is not a formal proof. A verified checker must establish:

1. completeness of the balanced ternary profile enumeration and affine quotient;
2. correctness of each rational reduced row space and incidence point;
3. nonzero maximal-rank minors and zero higher minors;
4. preservation of the data in characteristics at least 11;
5. distinct-point preservation and hence absence of new multiple intersections;
6. the exact line-union count and the normalization factor `q^2*(q-1)^2`.

The certificate is deliberately small in concept: 8 ratio cases, at most 39
lines in each case, and 7296 coefficient/augmented pair-matrix rank checks.
Individual minor witnesses can be regenerated with
`python3 code/verify.py --write --minors`.

## Integration boundary

Add sharper companion results to `lemma_15_4`; preserve the historical statement.
The existing `lemma_15_5` should only consume the new absolute exceptional count
after its actual expectation surplus and all quantifiers have been audited.
Update status ledgers only after successful formal compilation. Nothing in this
package certifies a new final density bound.
