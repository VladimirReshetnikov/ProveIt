# Proof audit

## Statements independent of the published limit-floor bound

1. Incomparability components form an ordinally ordered decomposition.
2. Friendly rank is additive over ordinal-indexed ordinal sums.
3. A connected incomparability graph has at most one maximal cut vertex.
4. Every finite poset has rank |P| - c(P), with an explicit witness.
5. f(alpha disjoint Gamma_m) = alpha + (m - 1), for any ordinal alpha and
   positive finite m.
6. f(omega disjoint omega) = omega*2 by direct residual calculation.
7. f((omega disjoint omega) disjoint 1) = omega*2 + 1.
8. The A/B example at ordinal omega proves nonfunctionality from the four
   invariants (o,h,w,f); no use of the limit-floor lemma is necessary.

## General infinite classification

The established external input is the limit-floor consequence of Vialard's
Theorem 4.5 (MFCS 2023), repeated as Theorem 5.4.4 in the 2024 thesis.
The classification does not use the unrestricted disjoint-sum identity
refuted in the article.

The remaining proof obligations are addressed in the manuscript:

- T(P) is an upset and is finite. An infinite subset of a wpo has an infinite
  increasing sequence, incompatible with finite principal upsets.
- Removing finitely many points does not change whether any remaining
  point's upset is finite. Thus the core is stable during tail deletion.
- Deleting a maximal element subtracts one from the finite terminal
  coefficient of maximal order type. The upper bound comes from the
  disjoint-sum/natural-sum law, not from an assumed identity for f.
- Full successor friendly rank forces an eligible maximal move. A
  nonmaximal move would permit two points to be appended to the residual
  maximal linear extension, exceeding the supposed maximal order type.
- A unique maximal cut vertex can occur only when that finite coefficient
  is one. Its deletion leaves no maximal element.
- Therefore n-1 maximal non-cut deletions preserve connectivity. The last
  tail point is still eligible, but deleting it may disconnect the core.
- The limit-floor bound supplies the lower value lambda+(n-1); full
  saturation occurs exactly when the stripped core retains type lambda.

## Boundary cases

- Empty P: c(P)=0 and f(P)=0.
- Singleton: one component and rank zero.
- A chain of arbitrary ordinal type: every point is friendless, so f=0.
- Infinite connected order with no finite tail: epsilon=0 automatically.
- General infinite disconnected orders: apply ordinal-sum additivity to
  components; do not apply the connected defect theorem globally.
- Finite arithmetic correction is written lambda+(n-epsilon). No ambiguous
  right/left ordinal subtraction is used in the new formulas.
- Mixed disjoint sums require a nonempty finite summand. Empty sums reduce
  to the unchanged other summand.
- Rectangular-grid formula requires both dimensions at least two.
- The multiset construction is the cancellation/replacement ordering, not
  injective multiset embedding.

## Actual execution

`results/verification.json` records the exhaustive run on 101,660 naturally
labeled posets with at most seven vertices and 25 grids. The reference
recurrence and graph formula are independent implementations. Witnesses are
checked against the original residuals, not merely against their lengths.
`results/unit_tests.txt` records ten passing unit tests.

No Lean, Isabelle, Coq, or other proof assistant was run. Finite execution
cannot certify infinite ranks: even [k] disjoint [k] has finite rank 2k-1,
whose supremum is omega, while the infinite two-chain rank is omega*2.

## Remaining review targets

Independent review should pay particular attention to the maximum/cut-vertex
lemma, the successor-attainment argument, and transfinite ordinal-sum
additivity at limit indices. The article contains full arguments for these,
but the present archive does not substitute a formal proof object for them.
