# Proof and scope audit

This file records what supports the manuscript's claims. It is not an
independent mathematical certification.

## Provenance

- Lipparini's arXiv:2505.00424v2, Problem 7.5, is the selected open-ended target.
- The sign-truncation rule already appears in Remark 7.6(3).
- The source already observes termination; the manuscript supplies an explicit
  ordinal rank instead of claiming to originate that observation.
- The manuscript's strongest proposed contributions are universal
  number-valuedness, the finite-short-perturbation estimate, and the exact
  finite/infinite-upgrade classification.
- The literature search was limited. Absence of a discovered overlapping paper
  is not evidence of exclusive priority.

## Dependency order

1. Define prefix truncation maps, their legal witnesses, and finite exemptions.
2. Construct an ordinal rank from the plus and minus sign heights. Every move
   strictly decreases it.
3. Show truncations commute. A nonidentity truncation can be legalized by moving
   its threshold to the earliest remaining unprotected sign.
4. Show the earlier witness in a pair of opposite moves survives. This proves
   left-option/right-option separation by induction on rank.
5. Deduce numerical game values, relabelling, zero insertion, negation, and
   agreement with finite sums and the source's ordinal operation.
6. Prove a finite-short-perturbation estimate by induction on the natural sum of
   two ranks. When one matched action is idle, a finite sign-length budget drops.
7. Evaluate constant dyadic sequences and finite defects by nested induction.
8. Describe all Left and Right options of the explicit convergent family.
9. For finite E, use integer simplicity. For infinite E, identify mutually
   cofinal and coinitial option sets, then use the standard omega-map cut.
10. Compare with an independently evaluated larger geometric sequence.

## Subtleties explicitly addressed

- A map can cease to be legal at its original threshold after another move.
  Commutation alone does not settle this issue. The proof includes threshold
  adjustment and a surviving-witness lemma.
- No argument assumes coordinatewise monotonicity of the broadcast value.
  Monotonicity of ordinary finite surreal addition is a separate standard fact.
- A 'finite error' is a surreal bounded by an integer, not necessarily an integer,
  real number, or infinitesimal.
- Every index family is a set, so the recursive option collections are sets.
- The ordinal rank uses ordinary ordinal arithmetic and finite natural sum.
  The dyadic multiples of omega use surreal field arithmetic.
- The exact constants theorem concerns 2^(-m), not all positive surreals.
- Finite-prefix evaluation is not a method for computing the infinite broadcast
  value; the manuscript explicitly disproves that limiting prescription.

## What was actually tested

The exact Python tests check finite strings, finite game cuts, commutation,
legal opposite-move diamonds, elementary invariances and dyadic sign formulas.
Their actual counts are in test_report.json. They all passed in the delivered
run. Tests do not prove any assertion quantified over all ordinal-length strings
or all infinite input sequences.

## Independent review still needed

A specialist should check the transfinite rank argument, the numerical comparison
induction in the finite-perturbation theorem, both nested inductions for constant
sequences, and the final coinitiality calculation. A formalization would provide
stronger assurance than these finite tests. No such independent review or
formalization is represented as having occurred.
